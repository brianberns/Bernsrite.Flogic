namespace Bernsrite.Flogic

/// A linear resolution derivation.
[<StructuredFormatDisplay("{String}")>]
type LinearInductionDerivation =
    {
        /// Positive proof of base case.
        BaseCase : Proof

        /// Postive proof of inductive case.
        InductiveCase : Proof
    }

    /// Display string.
    member this.ToString(level) =
        seq {

            yield ""
            yield "Base case:" |> Print.indent level
            yield this.BaseCase.ToString(level + 1)

            yield ""
            yield "Inductive case:" |> Print.indent level
            yield this.InductiveCase.ToString(level + 1)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

    /// Printable implementation.
    member this.Printable =
        {
            ToString = this.ToString
        }

module LinearInduction =

    /// Tries to prove the given formula using linear induction.
    let private tryProveRaw constant func subprover premises goal =

        let rec loop premises = function

                // e.g. ∀x.plus(x,0,x)
            | ForAll (variable, schema) as goal ->

                let subprover' =
                    Prover.combine loop subprover
                        |> Prover.pickSuccess

                opt {
                        // prove base case, e.g. plus(0,0,0)
                    let! baseCase =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (ConstantTerm constant)
                    let! baseProof = subprover' premises baseCase
                    assert(baseProof.Result)

                        // e.g. plus(s(x),0,s(x))
                    let! inductiveConclusion =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (Application (
                                    func, [| VariableTerm variable |]))

                        // prove inductive case, e.g. (plus(x,0,x) ⇒ plus(s(x),0,s(x))
                    let! inductiveProof =

                            // add base case to premises (since we proved it above)
                        let premises' = seq { yield! premises; yield baseCase }
                        let inductiveCase =
                            Implication (schema, inductiveConclusion)
                        subprover' premises' inductiveCase
                    assert(inductiveProof.Result)

                        // assemble result
                    let derivation =
                        {
                            BaseCase = baseProof
                            InductiveCase = inductiveProof
                        }
                    return Proof.create
                        premises goal true derivation.Printable
                }

            | _ -> None

        goal |> loop premises

    let tryProve language subprover premises goal =
        let constantOpt =
            language.Constants
                |> Seq.tryExactlyOne
        let functionOpt =
            language.Functions
                |> Seq.where (fun func ->
                    func.Arity = 1)
                |> Seq.tryExactlyOne
        match (constantOpt, functionOpt, goal) with
            | Some constant, Some func, ForAll _ ->
                tryProveRaw constant func subprover premises goal
            | _ ->
                subprover premises goal
