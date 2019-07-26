namespace Bernsrite.Flogic

type Theory =
    {
        /// Language used by this theory.
        Language : Language

        /// Axioms defined explicitly by this theory.
        Axioms : Formula[]
    }

module System =

    /// Linear induction prover for the given language.
    let inductionProver language : Prover =
        LinearInduction.tryProve language LinearResolution.tryProve

    /// Creates a strategic prover for the given language.
    let strategicProver language : Prover =
        Prover.serial [|
            inductionProver language
            LinearResolution.tryProve
        |] |> ConjuctionProver.tryProve

    /// Tries to prove the given formula.
    let tryProve theory =

        let language = theory.Language

        let premises =
            [|
                    // explicit premises
                yield! theory.Axioms

                    // equality axioms for this theory's language
                if language.Predicates |> Seq.contains Equality.predicate then
                    yield! Equality.equivalenceAxioms
                    yield! language |> Equality.substitutionAxioms
            |]

        strategicProver language premises
