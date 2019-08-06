namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main _ =

        let dtStart = DateTime.Now
        let proofOpt =
            "(=(+(0, y), +(y, 0)) ⇒ =(+(0, s(y)), +(s(y), 0)))"
                |> Language.parse Peano.theory.Language
                |> System.tryProve Peano.theory
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
