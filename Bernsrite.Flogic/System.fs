namespace Bernsrite.Flogic

type System =
    {
        /// Language used by this system.
        Language : Language

        /// Axioms defined explicitly by this system.
        Axioms : Formula[]
    }

module System =

    /// Tries to prove the given formula.
    let tryProve system =

        let language = system.Language

        let prover =
            Prover.serial [|
                LinearInduction.tryProve language LinearResolution.tryProve
                LinearResolution.tryProve
            |]

        let premises =
            [|
                    // explicit premises
                yield! system.Axioms

                    // equality axioms for this system's language
                if language.Predicates |> Seq.contains Equality.predicate then
                    yield! Equality.equivalenceAxioms
                    yield! language |> Equality.substitutionAxioms
            |]

        prover premises
