namespace Bernsrite.Flogic

type Theory =
    {
        /// Language used by this theory.
        Language : Language

        /// Axioms defined explicitly by this theory.
        Axioms : Formula[]
    }

module System =

    /// Creates a strategic prover for the given language.
    let strategicProver language : Prover =
        ConjuctionProver.tryProve
            **> LinearInduction.tryProve language
            **> LinearResolution.tryProve

    /// Tries to prove the given formula.
    let tryProve theory premises =
        let language = theory.Language
        strategicProver language
            [|
                    // theory's explicit premises
                yield! theory.Axioms

                    // implicit equality axioms for this theory's language
                if language.Predicates |> Seq.contains Equality.predicate then
                    yield! Equality.equivalenceAxioms
                    yield! language |> Equality.substitutionAxioms

                    // additional premises supplied
                yield! premises
            |]
