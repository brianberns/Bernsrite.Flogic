namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main _ =

        (*
        Assume:
            =(+(0,a), a)
        Then:
            +(0, s(a))
            = s(+(0,a))    [by a + s(b) = s(a + b)]
            = s(a)         [by assumption]
        *)

        let dtStart = DateTime.Now
        let proofOpt =
            // "∀x.=(+(0,x), x)"
            "(=(+(0,a), a) -> =(+(0,s(a)), s(a)))"
            // "(=(+(0,a), a) -> =(s(+(0,a)), s(a)))"
                |> Language.parse Peano.language
                |> System.tryProve Peano.system
        printfn "%A" proofOpt
        printfn "%A" (DateTime.Now - dtStart)

        0
