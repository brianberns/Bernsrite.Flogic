namespace Bernsrite.Flogic

type System =
    {
        /// Language used by this system.
        Language : Language

        /// Axioms defined explicitly by this system.
        Axioms : Formula[]
    }

module System =

    /// Generates linear induction axioms for the given formula.
    let private linearInductionAxioms
        baseConstant                 // e.g. 0
        (unaryFunction : Function)   // e.g. s(x)
        formula =                    // e.g. ∀x.pred(x,0,x)

        assert(unaryFunction.Arity = 1)

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
                                yield! inductiveConclusion |> loop   // recurse for nested ∀s
                            | None -> ()

                    | _ -> ()
            }

        formula
            |> loop
            |> Seq.toArray

    let tryProve system goal =
        let premises =
            let language = system.Language
            [|
                    // induction axioms
                if language.Constants.Length = 1 then
                    let constant =
                        language.Constants |> Array.exactlyOne
                    let functions =
                        goal
                            |> Formula.getFunctions
                            |> Map.keys
                    let predicates =
                        goal
                            |> Formula.getPredicates
                            |> Map.keys
                            |> Set.remove Equality.predicate
                    if functions.Count + predicates.Count > 0 then   // don't generate induction axioms for a goal that seems to be solely about equality
                        for func in language.Functions do
                            if func.Arity = 1 then
                                yield! linearInductionAxioms constant func goal

                    // equality axioms for this system's language
                if language.Predicates |> Seq.contains Equality.predicate then
                    yield! Equality.equivalenceAxioms

                    // explicit system axioms
                yield! system.Axioms
            |]
        Proof.tryProve premises goal
