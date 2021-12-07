module SimpleHashMap.Benchmarks 

open System
open BenchmarkDotNet
open BenchmarkDotNet.Attributes

open Clojure.Collections.Simple
open Clojure.Collections
open System.Collections.Generic

[<MemoryDiagnoser>]
[<MarkdownExporterAttribute.GitHub>]
type Benchmarks () =


    [<Params(1000, 10000)>]
    member val public count = 0 with get, set

    member val dict : Dictionary<int,int> = Dictionary() with get, set

    [<GlobalSetup>]
    member this.GlobalSetup() = 
        let rand = Random()
        for i = 1 to this.count-1 do
            let r = rand.Next()
            this.dict.[r] <- r 

    [<Benchmark>]
    member this.MakeSHMByAssoc() = 
        let mutable m = SimpleHashMap.Empty  :> IPersistentMap
        for key in this.dict.Keys do
            m <- m.assoc(key,key)
    
    [<Benchmark(Baseline=true)>]
    member this.MakePHMByAssoc() = 
        let mutable m = PersistentHashMap.Empty  :> IPersistentMap
        for key in this.dict.Keys do
            m <- m.assoc(key,key)

    [<Benchmark>]
    member this.MakePHMByTransient() = 
        PersistentHashMap.create(this.dict) |> ignore



