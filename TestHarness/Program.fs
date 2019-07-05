namespace Discover

open System

module Program =

    [<EntryPoint>]
    let main argv =

        let parser = Parser.makeParser ["a"; "b"]
        let premises =
            [
                "∀x.∀y.∀z.((p(x,y) ∧ p(y,z)) ⇒ p(x,z))"
                "∀x.p(x,a)"
                "∀y.p(a,y)"
            ] |> Seq.map (Parser.run parser)
        let goal = "∀x.∀y.p(x,y)" |> Parser.run parser

        let dtStart = DateTime.Now
        let proofOpt =
            Derivation.prove [3] premises goal
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
