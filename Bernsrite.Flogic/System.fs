namespace Bernsrite.Flogic

type System =
    {
        Language : Language
        Axioms : Formula[]
    }

module System =

    /// Generates linear induction axioms for the given formula.
    let private linearInductionAxioms
        baseConstant                             // e.g. 0
        (Function (_, arity) as unaryFunction)   // e.g. s(x)
        formula =                                // e.g. ∀x.pred(x,0,x)

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
                                yield! inductiveConclusion |> loop   // recurse for nested ∀s
                            | None -> ()

                    | _ -> ()
            }

        formula
            |> loop
            |> Seq.toArray

    /// Generates induction axioms for the given formula.
    let private inductionAxioms language formula =
        [|
            if language.Constants.Length = 1 then
                let constant =
                    language.Constants |> Array.exactlyOne
                let functions =
                    language.Functions
                        |> Seq.where (fun (Function (_, arity)) ->
                            arity = 1)
                for func in functions do
                    yield! linearInductionAxioms constant func formula
        |]

    let tryProve system goal =
        let annotatedPremises =
            seq {
                    // core system axioms
                for axiom in system.Axioms do
                    yield axiom, AxiomFormula

                    // equality axioms for this system's language
                if system.Language.Predicates |> Seq.contains Equality.predicate then
                    for axiom in Equality.equivalenceAxioms do
                        yield axiom, AxiomFormula
                    for axiom in system.Language |> Equality.substitutionAxioms do
                        yield axiom, AxiomFormula

                    // induction axioms
                for axiom in inductionAxioms system.Language goal do
                    yield axiom, InductionFormula
            }
        Proof.tryProveAnnotated annotatedPremises goal
