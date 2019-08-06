namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main _ =

        let dtStart = DateTime.Now
        let parse = Language.parse Peano.theory.Language
        let premises =
            [|
                "∀x.=(+(x,0), x)"
                "∀x.=(+(0,x), x)"
            |] |> Array.map parse
        let proofOpt =
            "(=(+(0, y), +(y, 0)) ⇒ =(+(0, s(y)), +(s(y), 0)))"
                |> parse
                |> System.tryProve Peano.theory premises
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
