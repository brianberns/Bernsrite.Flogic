namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main argv =

        let parser = Parser.makeParser ["harry"; "ralph"]
        let premises =
            [|
                "∀x.∀y.((h(x) ∧ d(y)) ⇒ f(x, y))"
                "∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y, z)))"
                "∀y.(g(y) ⇒ d(y))"
                "∀x.∀y.∀z.((f(x, y) ∧ f(y, z)) ⇒ f(x, z))"
                "h(harry)"
                "r(ralph)"
            |] |> Array.map (Parser.run parser)
        let goal = "f(harry, ralph)" |> Parser.run parser

        let dtStart = DateTime.Now
        let proofOpt =
            LinearResolution.tryProve premises goal
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
