namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main argv =

        let parser = Parser.makeParser ["0"]
        let parse = Parser.run parser

        let premises =
            [|
                "∀x.=(x, x)"
                "∀x.(~=(0, s(x)) & ~=(s(x), 0))"
                "∀x.∀y.(~=(x, y) ⇒ ~=(s(x), s(y)))"
                "∀y.+(0, y, y)"
                "∀x.∀y.∀z.(+(x, y, z) ⇒ +(s(x), y, s(z)))"
                "∀x.∀y.∀z.∀w.((+(x, y, z) & ~=(z, w)) ⇒ ~+(x, y, w))"
                "∀c.∀x.∀y.(((=(0, 0) & +(0, c, x)) & +(0, c, y)) ⇒ =(x, y))"
                "∀c.∀x.∀y.(((=(0, b) & +(0, c, x)) & +(b, c, y)) ⇒ =(x, y))"
                "(((=(0, s(b)) & +(0, 0, 0)) & +(s(b), 0, 0)) ⇒ =(0, 0))"
            |] |> Array.map parse
        let goal = parse "((((=(0, s(b)) & +(0, 0, 0)) & +(s(b), 0, y)) ⇒ =(0, y)) ⇒ (((=(0, s(b)) & +(0, 0, 0)) & +(s(b), 0, s(y))) ⇒ =(0, s(y))))"

        let dtStart = DateTime.Now
        let proofOpt =
            goal |> LinearResolution.tryProve premises
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
