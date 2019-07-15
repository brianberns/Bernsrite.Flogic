namespace Bernsrite.Flogic

open System

module Program =

    [<EntryPoint>]
    let main _ =

        let proofOpt =
            "∀a.∀b.∀c.∀x.∀y.(((=(a,b) ∧ +(a,c,x)) ∧ +(b,c,y)) ⇒ =(x,y))"
                |> Language.parse Peano.language
                |> Strategy.tryProve Peano.language Peano.axioms
        printfn "%A" proofOpt

        0
