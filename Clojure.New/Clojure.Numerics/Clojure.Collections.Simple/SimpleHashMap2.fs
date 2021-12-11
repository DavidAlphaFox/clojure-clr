namespace Clojure.Collections.Simple

open Clojure.Collections
open System.Collections
open System.Collections.Generic
open System

module private SHMNodeOps2 =

    let cloneAndSet (arr: 'T [], i: int, a: 'T) : 'T [] =
        let clone: 'T [] = downcast arr.Clone()
        clone.[i] <- a
        clone

    let removeEntry (arr: 'T [], i: int) : 'T [] =
        let newArr: 'T [] = Array.zeroCreate <| arr.Length - 1
        Array.Copy(arr, 0, newArr, 0, i)
        Array.Copy(arr, (i + 1), newArr, i, newArr.Length - i)
        newArr

    let getHash (o: obj) : int =
        match o with
        | null -> 0
        | _ -> o.GetHashCode()

    let mask (hash, shift) = (hash >>> shift) &&& 0x01f

    let bitPos (hash, shift) = 1 <<< mask (hash, shift)

    let bitCount (x) =
        let x = x - ((x >>> 1) &&& 0x55555555)

        let x =
            (((x >>> 2) &&& 0x33333333) + (x &&& 0x33333333))

        let x = (((x >>> 4) + x) &&& 0x0f0f0f0f)
        (x * 0x01010101) >>> 24

    let bitIndex (bitmap, bit) = bitCount (bitmap &&& (bit - 1))

    let hashToIndex (hash: int) (shift: int) (bitmap: int) : int option =
        let bit = bitPos (hash, shift)

        if bit &&& bitmap = 0 then
            None
        else
            bitIndex (bitmap, bit) |> Some

    let pcequiv (k1: obj, k2: obj) =
        match k1, k2 with
        | :? IPersistentCollection as pc1, _ -> pc1.equiv (k2)
        | _, (:? IPersistentCollection as pc2) -> pc2.equiv (k1)
        | _ -> k1.Equals(k2)

    let equiv (k1: obj, k2: obj) =
        if Object.ReferenceEquals(k1, k2) then
            true
        elif isNull k1 then
            false
        else
            pcequiv (k1, k2)

open SHMNodeOps2
open System.Reflection

// pick these up from original SimpleHashMap

//type Box(init) =
//    let mutable value: bool = init
//    new() = Box(false)

//    member _.set() = value <- true
//    member _.reset() = value <- false
//    member _.isSet = value
//    member _.isNotSet = not value

//type KVTranformFn<'T> = obj * obj -> 'T

type BNodeEntry2 =
    | KeyValue of Key: obj * Value: obj
    | Node of Node: SHMNode2

and [<ReferenceEquality>] SHMNode2 =
    | ArrayNode2 of Count: int ref * Nodes: (SHMNode2 option) []
    | BitmapNode2 of Bitmap: int ref * Entries: BNodeEntry2 [] ref
    | CollisionNode2 of Hash: int * Count: int ref * KVs: MapEntry [] ref

    static member EmptyBitmapNode = BitmapNode2(ref 0, ref Array.empty<BNodeEntry2>)

    static member tryFindCNodeIndex(key: obj, kvs: MapEntry []) =
        kvs
        |> Array.tryFindIndex (fun kv -> equiv ((kv :> IMapEntry).key (), key))

    static member createNode (shift: int) (key1: obj) (val1: obj) (key2hash: int) (key2: obj) (val2: obj) : SHMNode2 =
        let key1hash = hash (key1)

        if key1hash = key2hash then
            CollisionNode2(
                key1hash,
                ref 2,
                ref [| MapEntry(key1, val1)
                       MapEntry(key2, val2) |]
            )
        else
            let box = Box()

            let n1 =
                SHMNode2.EmptyBitmapNode.assoc shift key1hash key1 val1 box

            n1.assoc shift key2hash key2 val2 box

    member this.getNodeSeq() =
        match this with
        | ArrayNode2 (Count = count; Nodes = nodes) -> ArrayNode2Seq.create (nodes, 0)
        | BitmapNode2 (Bitmap = bitmap; Entries = entries) -> BitmapNode2Seq.create (entries.Value, 0)
        | CollisionNode2 (Hash = hash; Count = count; KVs = kvs) -> CollisionNode2Seq.create (kvs.Value, 0)

    member this.find (shift: int) (hash: int) (key: obj) : IMapEntry option =
        match this with
        | ArrayNode2 (Count = count; Nodes = nodes) ->
            let idx = mask (hash, shift)

            match nodes.[idx] with
            | None -> None
            | Some node -> node.find (shift + 5) hash key
        | BitmapNode2 (Bitmap = bitmap; Entries = entries) ->
            match hashToIndex hash shift bitmap.Value with
            | None -> None
            | Some idx ->
                match entries.Value.[idx] with
                | KeyValue (Key = k; Value = v) ->
                    if equiv (key, k) then
                        (MapEntry(k, v) :> IMapEntry) |> Some
                    else
                        None
                | Node (Node = node) -> node.find (shift + 5) hash key
        | CollisionNode2 (Hash = hash; Count = count; KVs = kvs) ->
            match SHMNode2.tryFindCNodeIndex (key, kvs.Value) with
            | None -> None
            | Some idx -> Some(upcast kvs.Value.[idx])


    member this.find2 (shift: int) (hash: int) (key: obj) (notFound: obj) : obj =
        match this with
        | ArrayNode2 (Count = count; Nodes = nodes) ->
            let idx = mask (hash, shift)

            match nodes.[idx] with
            | None -> notFound
            | Some node -> node.find2 (shift + 5) hash key notFound

        | BitmapNode2 (Bitmap = bitmap; Entries = entries) ->
            match hashToIndex hash shift bitmap.Value with
            | None -> notFound
            | Some idx ->
                match entries.Value.[idx] with
                | KeyValue (Key = k; Value = v) -> if equiv (key, k) then v else notFound
                | Node (Node = node) -> node.find2 (shift + 5) hash key notFound

        | CollisionNode2 (Hash = hash; Count = count; KVs = kvs) ->
            match SHMNode2.tryFindCNodeIndex (key, kvs.Value) with
            | None -> notFound
            | Some idx -> (kvs.Value.[idx] :> IMapEntry).value ()

    member this.assoc (shift: int) (hash: int) (key: obj) (value: obj) (addedLeaf: Box) : SHMNode2 =
        match this with
        | ArrayNode2 (Count = count; Nodes = nodes) ->
            let idx = mask (hash, shift)

            match nodes.[idx] with
            | None ->
                let newNode =
                    SHMNode2.EmptyBitmapNode.assoc (shift + 5) hash key value addedLeaf

                ArrayNode2(ref (count.Value + 1), cloneAndSet (nodes, idx, Some newNode))
            | Some node ->
                let newNode =
                    node.assoc (shift + 5) hash key value addedLeaf

                if newNode = node then
                    this
                else
                    ArrayNode2(count, cloneAndSet (nodes, idx, Some newNode))

        | BitmapNode2 (Bitmap = bitmap; Entries = entries) ->
            match hashToIndex hash shift bitmap.Value with
            | None ->
                let n = bitCount (bitmap.Value)

                if n >= 16 then
                    let nodes: SHMNode2 option [] = Array.zeroCreate 32
                    let jdx = mask (hash, shift)

                    nodes.[jdx] <-
                        SHMNode2.EmptyBitmapNode.assoc (shift + 5) hash key value addedLeaf
                        |> Some

                    let mutable j = 0

                    for i = 0 to 31 do
                        if ((bitmap.Value >>> i) &&& 1) <> 0 then
                            nodes.[i] <-
                                match entries.Value.[j] with
                                | KeyValue (Key = k; Value = v) ->
                                    SHMNode2.EmptyBitmapNode.assoc (shift + 5) (getHash k) k v addedLeaf
                                    |> Some
                                | Node (Node = node) -> node |> Some

                            j <- j + 1

                    ArrayNode2(ref (n + 1), nodes)

                else
                    let bit = bitPos (hash, shift)
                    let idx = bitIndex (bitmap.Value, bit)
                    let newArray: BNodeEntry2 [] = Array.zeroCreate (n + 1)
                    Array.Copy(entries.Value, 0, newArray, 0, idx)
                    newArray.[idx] <- KeyValue(key, value)
                    Array.Copy(entries.Value, idx, newArray, idx + 1, n - idx)
                    addedLeaf.set ()
                    BitmapNode2(ref (bitmap.Value ||| bit), ref newArray)

            | Some idx ->
                let entry = entries.Value.[idx]

                match entry with
                | KeyValue (Key = k; Value = v) ->
                    if equiv (key, k) then
                        if value = v then
                            this
                        else
                            BitmapNode2(ref bitmap.Value, ref (cloneAndSet (entries.Value, idx, KeyValue(key, value))))
                    else
                        addedLeaf.set ()

                        let newNode =
                            SHMNode2.createNode (shift + 5) k v hash key value

                        BitmapNode2(ref bitmap.Value, ref (cloneAndSet (entries.Value, idx, Node(newNode))))
                | Node (Node = node) ->
                    let newNode =
                        node.assoc (shift + 5) hash key value addedLeaf

                    if newNode = node then
                        this
                    else
                        BitmapNode2(ref bitmap.Value, ref (cloneAndSet (entries.Value, idx, Node(newNode))))

        | CollisionNode2 (Hash = h; Count = count; KVs = kvs) ->
            if hash = h then
                match SHMNode2.tryFindCNodeIndex (key, kvs.Value) with
                | Some idx ->
                    let kv = kvs.Value.[idx] :> IMapEntry

                    if kv.value () = value then
                        this
                    else
                        CollisionNode2(hash, ref count.Value, ref (cloneAndSet (kvs.Value, idx, MapEntry(key, value))))
                | None ->
                    let newArray: MapEntry [] = count.Value + 1 |> Array.zeroCreate
                    Array.Copy(kvs.Value, 0, newArray, 0, count.Value)
                    newArray.[count.Value] <- MapEntry(key, value)
                    addedLeaf.set ()
                    CollisionNode2(hash, ref (count.Value + 1), ref newArray)
            else
                BitmapNode2(
                    ref (bitPos (hash, shift)),
                    ref [| Node(this) |]
                )
                    .assoc
                    shift
                    h
                    key
                    value
                    addedLeaf

    // TODO: do this with sequence functions?
    static member pack (count: int) (nodes: SHMNode2 option []) (idx: int) : SHMNode2 =
        let newArray: BNodeEntry2 [] = count - 1 |> Array.zeroCreate
        let mutable j = 0
        let mutable bitmap = 0

        for i = 0 to idx - 1 do
            match nodes.[i] with
            | None -> ()
            | Some n ->
                newArray.[j] <- Node n
                bitmap <- bitmap ||| 1 <<< i
                j <- j + 1

        for i = idx + 1 to nodes.Length - 1 do
            match nodes.[i] with
            | None -> ()
            | Some n ->
                newArray.[j] <- Node n
                bitmap <- bitmap ||| 1 <<< i
                j <- j + 1

        BitmapNode2(ref bitmap, ref newArray)


    member this.without (shift: int) (hash: int) (key: obj) : SHMNode2 option =
        match this with
        | ArrayNode2 (Count = count; Nodes = nodes) ->
            let idx = mask (hash, shift)

            match nodes.[idx] with
            | None -> this |> Some
            | Some node ->
                match node.without (shift + 5) hash key with
                | None -> // this branch got deleted
                    if count.Value <= 8 then
                        SHMNode2.pack count.Value nodes idx |> Some // shrink
                    else
                        ArrayNode2(ref (count.Value - 1), cloneAndSet (nodes, idx, None))
                        |> Some // zero out this entry
                | Some newNode ->
                    if newNode = node then
                        this |> Some
                    else
                        ArrayNode2(ref (count.Value - 1), cloneAndSet (nodes, idx, Some newNode))
                        |> Some

        | BitmapNode2 (Bitmap = bitmap; Entries = entries) ->
            match hashToIndex hash shift bitmap.Value with
            | None -> this |> Some
            | Some idx ->
                let entry = entries.Value.[idx]

                match entry with
                | KeyValue (Key = k; Value = v) ->
                    if equiv (k, key) then
                        let bit = bitPos (hash, shift)

                        if bitmap.Value = bit then // only one entry
                            None
                        else
                            BitmapNode2( ref (bitmap.Value ^^^ bit), ref (removeEntry (entries.Value, idx)))
                            |> Some
                    else
                        this |> Some
                | Node (Node = node) ->
                    match node.without (shift + 5) hash key with
                    | None -> this |> Some
                    | Some n ->
                        if n = node then
                            this |> Some
                        else
                            BitmapNode2(ref bitmap.Value, ref (cloneAndSet (entries.Value, idx, Node(n))))
                            |> Some

        | CollisionNode2 (Hash = h; Count = count; KVs = kvs) ->
            match SHMNode2.tryFindCNodeIndex (key, kvs.Value) with
            | None -> this |> Some
            | Some idx ->
                if count.Value = 1 then
                    None
                else
                    CollisionNode2(h, ref (count.Value - 1), ref (removeEntry (kvs.Value, idx)))
                    |> Some


    member this.iteratorT(d: KVTranformFn<'T>) : IEnumerator<'T> =
        match this with
        | ArrayNode2 (Nodes = nodes) ->
            let s =
                seq {
                    for onode in nodes do
                        match onode with
                        | None -> ()
                        | Some node ->
                            let ie = node.iteratorT (d)

                            while ie.MoveNext() do
                                yield ie.Current
                }

            s.GetEnumerator()
        | BitmapNode2 (Bitmap = bitmap; Entries = entries) ->
            let s =
                seq {
                    for entry in entries.Value do
                        match entry with
                        | KeyValue (Key = k; Value = v) -> yield d (k, v)
                        | Node (Node = node) ->
                            let ie = node.iteratorT (d)

                            while ie.MoveNext() do
                                yield ie.Current
                }

            s.GetEnumerator()
        | CollisionNode2 (Hash = h; Count = count; KVs = kvs) ->
            let s =
                seq {
                    for kv in kvs.Value do
                        let me = kv :> IMapEntry
                        yield d (me.key (), me.value ())
                }

            s.GetEnumerator()

and ArrayNode2Seq(nodes: (SHMNode2 option) [], idx: int, s: ISeq) =
    inherit ASeq()


    static member create(nodes: (SHMNode2 option) [], idx: int) : ISeq =
        if idx >= nodes.Length then
            null
        else
            match nodes.[idx] with
            | Some (node) ->
                match node.getNodeSeq () with
                | null -> ArrayNode2Seq.create (nodes, idx + 1)
                | s -> ArrayNode2Seq(nodes, idx, s)
            | None -> ArrayNode2Seq.create (nodes, idx + 1)

    interface ISeq with
        member _.first() = s.first ()

        member _.next() =
            match s.next () with
            | null -> ArrayNode2Seq.create (nodes, idx + 1)
            | s1 -> ArrayNode2Seq(nodes, idx, s1)


and BitmapNode2Seq(entries: BNodeEntry2 [], idx: int, seq: ISeq) =
    inherit ASeq()

    static member create(entries: BNodeEntry2 [], idx: int) : ISeq =
        if idx >= entries.Length then
            null
        else
            match entries.[idx] with
            | KeyValue (_, _) -> BitmapNode2Seq(entries, idx, null)
            | Node (Node = node) ->
                match node.getNodeSeq () with
                | null -> BitmapNode2Seq.create (entries, idx + 1)
                | s -> BitmapNode2Seq(entries, idx, s)

    interface ISeq with
        member _.first() =
            match entries.[idx] with
            | KeyValue (Key = k; Value = v) -> MapEntry(k, v)
            | Node (Node = _) -> seq.first ()

        member _.next() =
            match entries.[idx] with
            | KeyValue (_, _) -> BitmapNode2Seq.create (entries, idx + 1)
            | Node (_) ->
                match seq.next () with
                | null -> BitmapNode2Seq.create (entries, idx + 1)
                | s -> BitmapNode2Seq(entries, idx, s)

and CollisionNode2Seq(kvs: MapEntry [], idx: int) =
    inherit ASeq()

    static member create(kvs: MapEntry [], idx: int) : ISeq =
        if idx >= kvs.Length then
            null
        else
            CollisionNode2Seq(kvs, idx)

    interface ISeq with
        member _.first() = kvs.[idx]
        member _.next() = CollisionNode2Seq.create (kvs, idx + 1)


type NotFoundSentinel2 = | NFS2

type SimpleHashMap2 =
    | Empty
    | Rooted of Count: int * Node: SHMNode2

    static member notFoundValue = NFS2

    interface Counted with
        member this.count() =
            match this with
            | Empty -> 0
            | Rooted (Count = c) -> c

    interface Seqable with
        member this.seq() =
            match this with
            | Empty -> null
            | Rooted (Node = n) -> n.getNodeSeq ()

    interface IPersistentCollection with
        member this.count() = (this :> Counted).count ()

        member this.cons(o) =
            upcast (this :> IPersistentMap).cons (o)

        member this.empty() = upcast Empty

        member this.equiv(o) = // a bit of a simplification from the Clojure/ClojureCLR version
            match o with
            | :? IDictionary as d ->
                if d.Count
                   <> (this :> IPersistentCollection).count () then
                    false
                else
                    let rec step (s: ISeq) =
                        if isNull s then
                            true
                        else
                            let me: IMapEntry = downcast s.first ()

                            if
                                d.Contains(me.key ())
                                && Util.equiv (me.value (), d.[me.key ()])
                            then
                                step (s.next ())
                            else
                                false

                    step ((this :> Seqable).seq ())
            | _ -> false


    interface ILookup with
        member this.valAt(k) = (this :> ILookup).valAt (k, null)

        member this.valAt(k, nf) =
            match this with
            | Empty -> nf
            | Rooted (Node = n) -> n.find2 0 (hash k) k nf

    interface Associative with
        member this.containsKey(k) =
            match this with
            | Empty -> false
            | Rooted (Node = n) ->
                (n.find2 0 (hash k) k SimpleHashMap2.notFoundValue)
                <> (upcast SimpleHashMap2.notFoundValue)

        member this.entryAt(k) =
            match this with
            | Empty -> null
            | Rooted (Node = n) ->
                match n.find 0 (hash k) k with
                | None -> null
                | Some me -> me

        member this.assoc(k, v) =
            upcast (this :> IPersistentMap).assoc (k, v)

    interface IPersistentMap with
        member this.count() = (this :> Counted).count ()

        member this.assocEx(k, v) =
            if (this :> Associative).containsKey (k) then
                raise
                <| InvalidOperationException("Key already present")

            (this :> IPersistentMap).assoc (k, v)

        member this.cons(o) =
            match o with
            | null -> upcast this
            | :? IMapEntry as e ->
                (this :> IPersistentMap)
                    .assoc (e.key (), e.value ())
            | :? DictionaryEntry as e -> (this :> IPersistentMap).assoc (e.Key, e.Value)
            | _ when
                o.GetType().IsGenericType
                && o.GetType().Name = "KeyValuePair`2"
                ->
                let t = o.GetType()

                let k =
                    t.InvokeMember("Key", BindingFlags.GetProperty, null, o, null)

                let v =
                    t.InvokeMember("Value", BindingFlags.GetProperty, null, o, null)

                (this :> IPersistentMap).assoc (k, v)
            | :? IPersistentVector as v ->
                if v.count () = 2 then
                    (this :> IPersistentMap)
                        .assoc (v.nth (0), v.nth (1))
                else
                    raise
                    <| ArgumentException("o", "Vector arg to map cons must be a pair")
            | _ ->
                let rec step (s: ISeq) (m: IPersistentMap) =
                    if isNull s then
                        m
                    else
                        let me = s.first () :?> IMapEntry
                        step (s.next ()) (m.assoc (me.key (), me.value ()))

                step (RT.seq (o)) this

        member this.assoc(k, v) =
            let addedLeaf = Box()

            let rootToUse =
                match this with
                | Empty -> SHMNode2.EmptyBitmapNode
                | Rooted (Node = n) -> n

            let newRoot = rootToUse.assoc 0 (hash k) k v addedLeaf

            if newRoot = rootToUse then
                upcast this
            else
                let count = (this :> Counted).count ()

                let updatedCount =
                    if addedLeaf.isSet then
                        count + 1
                    else
                        count


                upcast Rooted(updatedCount, newRoot)

        member this.without(k) =
            match this with
            | Empty -> upcast this
            | Rooted (Count = c; Node = n) ->
                match n.without 0 (hash k) k with
                | None -> Empty
                | Some newRoot ->
                    if newRoot = n then upcast this
                    elif c = 1 then upcast Empty
                    else upcast Rooted(c - 1, newRoot)

    member this.MakeEnumerator(d: KVTranformFn<Object>) : IEnumerator =
        match this with
        | Empty -> upcast Seq.empty.GetEnumerator()
        | Rooted (Node = n) -> upcast n.iteratorT (d)

    member this.MakeEnumeratorT<'T>(d: KVTranformFn<'T>) : IEnumerator<'T> =
        match this with
        | Empty -> Seq.empty.GetEnumerator()
        | Rooted (Node = n) -> n.iteratorT (d)

    interface IEnumerable<IMapEntry> with
        member this.GetEnumerator() =
            this.MakeEnumeratorT<IMapEntry>(fun (k, v) -> upcast MapEntry.create (k, v))

    interface IEnumerable with
        member this.GetEnumerator() =
            this.MakeEnumerator(fun (k, v) -> upcast MapEntry.create (k, v))

    interface IMapEnumerable with
        member this.keyEnumerator() = this.MakeEnumerator(fun (k, v) -> k)
        member this.valEnumerator() = this.MakeEnumerator(fun (k, v) -> v)

    //interface IFn with
    //    override this.invoke(arg1) = (this:>ILookup).valAt(arg1)
    //    override this.invoke(arg1,arg2) = (this:>ILookup).valAt(arg1,arg2)

    static member create(other: IDictionary) : IPersistentMap =
        let mutable ret = Empty :> IPersistentMap

        for o in other do
            let de = o :?> DictionaryEntry
            ret <- ret.assoc (de.Key, de.Value)

        ret

    static member create1(init: IList) : IPersistentMap =
        let mutable ret = Empty :> IPersistentMap
        let ie = init.GetEnumerator()

        while ie.MoveNext() do
            let key = ie.Current

            if not (ie.MoveNext()) then
                raise
                <| ArgumentException("init", "No value supplied for " + key.ToString())

            let value = ie.Current
            ret <- ret.assoc (key, value)

        ret
