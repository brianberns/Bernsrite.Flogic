namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main _ =

        let dtStart = DateTime.Now
        let proofOpt =
            "∀x.=(+(0,x), x)"
            // "(=(+(0,a), a) -> =(+(0,s(a)), s(a)))"
                |> Language.parse Peano.language
                |> System.tryProve Peano.theory
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
