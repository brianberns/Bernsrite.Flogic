namespace Discover

module Program =

    [<EntryPoint>]
    let main argv =

        let parser = Parser.makeParser ["harry"; "ralph"; "skolem1"]
        let premises =
            [
                "∀x.∀y.((h(x) ∧ d(y)) ⇒ f(x, y))"
                "∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y, z)))"
                "∀y.(g(y) ⇒ d(y))"
                "∀x.∀y.∀z.((f(x, y) ∧ f(y, z)) ⇒ f(x, z))"
                "h(harry)"
                "r(ralph)"
            ] |> Seq.map (Parser.run parser)
        let goal = "f(harry, ralph)" |> Parser.run parser
        let proofOpt =
            Derivation.prove premises goal
        printfn "%A" proofOpt

        0
