namespace Discover

open System

module Program =

    [<EntryPoint>]
    let main argv =

        // https://www.cs.utexas.edu/users/novak/reso.html
        let parser = Parser.makeParser ["John"]
        let premises =
            [|
                "∀x.(HOUND(x) → HOWL(x))"
                "∀x.∀y.((HAVE (x,y) ∧ CAT (y)) → ¬∃z.(HAVE(x,z) ∧ MOUSE(z)))"
                "∀x.(LS(x) → ¬∃y.(HAVE (x,y) ∧ HOWL(y)))"
                "∃x.(HAVE(John,x) ∧ (CAT(x) ∨ HOUND(x)))"
            |] |> Array.map (Parser.run parser)
        let goal = "(LS(John) → ¬∃z.(HAVE(John,z) ∧ MOUSE(z)))" |> Parser.run parser

        let dtStart = DateTime.Now
        let proofOpt =
            Derivation.prove [8] premises goal
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
