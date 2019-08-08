namespace Bernsrite.Flogic

/// A conjuction derivation.
[<StructuredFormatDisplay("{String}")>]
type ConjunctionDerivation =
    {
        /// First case.
        Case1 : Proof

        /// Second case.
        Case2 : Proof
    }

    /// Display string.
    member this.ToString(level) =
        seq {

            yield ""
            yield "First case:" |> Print.indent level
            yield this.Case1.ToString(level + 1)

            yield ""
            yield "Second case:" |> Print.indent level
            yield this.Case2.ToString(level + 1)

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

module ConjuctionProver =

    /// Tries to prove the given formula as a conjunction of two sub-cases.
    let tryProve subprover premises goal =

        let rec rebuild variables formula =
            match variables with
                | variable :: tail ->
                    ForAll (variable, formula)
                        |> rebuild tail
                | [] -> formula

        let rec split variables = function
            | Biconditional (formula1, formula2) ->
                And (
                    Implication (formula1, formula2) |> rebuild variables,
                    Implication (formula2, formula1) |> rebuild variables)
                    |> Some
            | ForAll (variable, formula) ->
                formula |> split (variable :: variables)
            | _ -> None

        let rec loop = function

                // prove P, then prove Q
            | And (formula1, formula2) ->
                opt {
                    let! proof1 = formula1 |> subprover premises
                    let! proof2 = formula2 |> subprover premises
                    let derivation =
                        {
                            Case1 = proof1
                            Case2 = proof2
                        }
                    return Proof.create
                        premises
                        goal
                        (proof1.Result && proof2.Result)
                        derivation.Printable
                }

                // ∀x.∀y.(P(x,y) <-> Q(x,y))
                // prove ∀x.∀y.(P(x,y) -> Q(x,y)) & ∀x.∀y.(Q(x,y) -> P(x,y))
            | ForAll (variable, formula) ->
                splitLoop [variable] formula

                // prove (P -> Q) & (Q -> P)
            | Biconditional _ as formula ->
                splitLoop [] formula

            | _ -> None

        and splitLoop variables formula =
            opt {
                let! formula' =
                    formula |> split variables
                return! formula' |> loop
            }

        goal |> loop
