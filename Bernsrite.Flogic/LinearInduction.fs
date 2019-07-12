namespace Bernsrite.Flogic

type Language =
    {
        Constants : Constant[]
        Functions : Function[]
        Predicates : Predicate[]
    }

module Language =

    /// Creates a parser for the given language.
    let makeParser language : Parser<_> =
        language.Constants
            |> Array.map (fun (Constant name) -> name)
            |> Parser.makeParser

type LinearInductionDerivation =
    {
        BaseCase : Proof
        InductiveCase : Proof
    }

module LinearInduction =

    /// Tries to prove the given formula using linear induction.
    let private tryProveRaw constant func (subprover : Prover) premises goal =

        let rec loop premises = function

                // e.g. ∀x.plus(x,0,x)
            | ForAll (variable, schema) as goal ->
                opt {
                        // prove base case, trying recursive induction first
                        // e.g. plus(0,0,0)
                    let! baseCase =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (ConstantTerm constant)
                    let! baseProof =
                        Prover.combine loop subprover premises baseCase

                        // e.g. plus(s(x),0,s(x))
                    let! inductiveConclusion =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (Application (
                                    func, [| VariableTerm variable |]))

                        // prove inductive case
                        // e.g. (plus(x,0,x) ⇒ plus(s(x),0,s(x))
                    let! inductiveProof =

                            // add base case to premises (since we proved it above)
                        let premises' = seq { yield! premises; yield baseCase }

                            // assume antecedent for recursive proof
                        inductiveConclusion
                            |> loop (seq { yield! premises'; yield schema })

                                // otherwise, try to prove the full implication without assuming the antecedent
                                // see https://math.stackexchange.com/questions/3290370/first-order-logic-and-peano-arithmetic-paradox
                            |> Option.orElseWith (fun () ->
                                Implication (schema, inductiveConclusion)
                                    |> subprover premises')

                    return {
                        Premises = premises |> Seq.toArray
                        Goal = goal
                        Evidence =
                            {
                                BaseCase = baseProof
                                InductiveCase = inductiveProof
                            }
                    }
                }
            | _ -> None

        goal |> loop premises

    /// Tries to prove the given formula using linear induction.
    let tryProve language subprover premises goal =
        let constantOpt =
            language.Constants
                |> Seq.tryExactlyOne
        let functionOpt =
            language.Functions
                |> Seq.where (fun (Function (_, arity)) ->
                    arity = 1)
                |> Seq.tryExactlyOne
        match (constantOpt, functionOpt) with
            | Some constant, Some func ->
                tryProveRaw constant func subprover premises goal
            | _ -> None

module Strategy =

    /// Tries to prove the given formula.
    let tryProve language =
        Prover.serial [|
            LinearInduction.tryProve language LinearResolution.tryProve
            LinearResolution.tryProve
        |]
