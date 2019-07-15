namespace Bernsrite.Flogic

module Peano =

    let zero = Constant "0"

    let successor = Function ("s", 1)

    let axiomGenerator formula =
    
        let rec loop formula =
            seq {

                match formula with

                        // e.g. ∀x.pred(x,0,x)
                    | ForAll (variable, schema) as goal ->
                        let pairOpt =
                            opt {
                                    // e.g. pred(0,0,0)
                                let! baseCase =
                                    schema
                                        |> Formula.trySubstitute
                                            variable
                                            (ConstantTerm zero)

                                    // e.g. pred(s(x),0,s(x))
                                let! inductiveConclusion =
                                    schema
                                        |> Formula.trySubstitute
                                            variable
                                            (Application (
                                                successor,
                                                [| VariableTerm variable |]))

                                    // e.g. ∀x.(pred(x,0,x) ⇒ pred(s(x),0,s(x)))
                                let inductiveCase =
                                    ForAll (
                                        variable,
                                        Implication (schema, inductiveConclusion))

                                    // pred(0,0,0) ∧ ∀x.(pred(x,0,x) ⇒ pred(s(x),0,s(x))) ⇒ ∀x.pred(x,0,x)
                                let axiom =
                                    Implication (
                                        And (baseCase, inductiveCase),
                                        goal)

                                return axiom, inductiveConclusion
                            }
                        match pairOpt with
                            | Some (axiom, inductiveConclusion) ->
                                yield axiom
                                yield! inductiveConclusion |> loop
                            | None -> ()

                    | _ -> ()
            }

        formula
            |> loop
            |> Seq.toArray

    let language =
        Language.create
            [| zero |]
            [|
                successor
                Function ("+", 2)
                Function ("*", 2)
            |]
            [| Equality.predicate |]
            axiomGenerator

    let private parse = Array.map (Language.parse language)

    let plusAxioms =
        parse [|
            "∀x.=(+(x,0), x)"
            "∀x.∀y.=(+(x,s(y)), s(+(x,y)))"
        |]

    let axioms =
        [|
            yield! Equality.getAxioms language
            yield! plusAxioms
        |]
