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

    /// Tries to prove the given formula.
    let tryProve theory =

        let language = theory.Language

        let prover =
            Prover.serial [|

                    // induction + resolution
                inductionProver theory.Language

                    // resolution alone
                LinearResolution.tryProve
            |]

        let premises =
            [|
                    // explicit premises
                yield! theory.Axioms

                    // equality axioms for this theory's language
                if language.Predicates |> Seq.contains Equality.predicate then
                    yield! Equality.equivalenceAxioms
                    yield! language |> Equality.substitutionAxioms
            |]

        prover premises
