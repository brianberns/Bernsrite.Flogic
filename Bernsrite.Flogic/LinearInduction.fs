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
            Object = this
            ToString = this.ToString
        }

module LinearInduction =

    /// Tries to prove the given formula using linear induction.
    let private tryProveRaw constant func (subprover : Prover) premises goal =

        /// Picks only a successful proof.
        let pickSuccess proofOpt =
            proofOpt
                |> Option.bind (fun proof ->
                    if proof.Result then Some proof
                    else None)

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
                            |> pickSuccess

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
                            |> pickSuccess

                    return Proof.create
                        premises
                        goal
                        true
                        {
                            BaseCase = baseProof
                            InductiveCase = inductiveProof
                        }.Printable
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
