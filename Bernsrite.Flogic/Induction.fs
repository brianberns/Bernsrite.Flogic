namespace Bernsrite.Flogic

module Induction =

    /// Generates linear induction axioms for the given formula.
    let linearInductionAxioms
        baseConstant
        (Function (_, arity) as unaryFunction)
        formula =

        assert(arity = 1)

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
                                            (ConstantTerm baseConstant)

                                    // e.g. pred(s(x),0,s(x))
                                let! inductiveConclusion =
                                    schema
                                        |> Formula.trySubstitute
                                            variable
                                            (Application (
                                                unaryFunction,
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
