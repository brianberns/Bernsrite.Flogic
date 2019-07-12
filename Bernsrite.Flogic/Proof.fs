namespace Bernsrite.Flogic

open System

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

/// Derivation of a proof.
type IDerivation =
    abstract member ToString : int -> string

/// Information about a successsful proof.
[<StructuredFormatDisplay("{String}")>]
type ProofSuccess =
    {
        /// Premises used by this proof.
        Premises : Formula[]

        /// Goal proved.
        Goal : Formula

        /// Derivation of the proof.
        Derivation : IDerivation
    }

    /// Display string.
    member this.ToString(level) =
        seq {

            yield ""
            yield sprintf "Goal: %A" this.Goal |> Print.indent level

            yield ""
            yield "Premises:" |> Print.indent level
            for premise in this.Premises do
                yield premise |> Print.indent (level + 1)

            yield this.Derivation.ToString(level)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module ProofSuccess =

    /// Creates a proof success.
    let create premises goal evidence =
        {
            Premises = premises |> Seq.toArray
            Goal = goal
            Derivation = evidence
        }

/// Result of an attempted proof.
[<StructuredFormatDisplay("{String}")>]
type ProofResult =

    /// Goal was proved.
    | Proved of ProofSuccess

    /// Goal was disproved. Negation of the goal was proved.
    | Disproved of ProofSuccess

    /// Goal could not be proved or disproved.
    | Undecided

    /// Display string.
    member this.ToString(level) =
        seq {
            match this with
                | Proved success ->
                    yield success.ToString(level)
                    yield ""
                    yield "Proved" |> Print.indent level
                | Disproved success ->
                    yield success.ToString(level)
                    yield ""
                    yield "Disproved" |> Print.indent level
                | Undecided -> yield "Undecided" |> Print.indent level
        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

/// A prover is a function that can attempt proofs.
type Prover = seq<Formula> (*premises*) -> Formula (*goal*) -> ProofResult

module Prover =

    /// Creates a serial prover from the given provers.
    let serial provers : Prover =
        fun premises goal ->
            provers
                |> Seq.tryPick (fun (prover : Prover) ->
                    let result = prover premises goal
                    match result with
                        | Proved _
                        | Disproved _ -> Some result
                        | Undecided -> None)
                |> function
                    | Some (Proved _ as result)
                    | Some (Disproved _ as result) -> result
                    | _ -> Undecided

    /// Combines the given provers in series.
    let combine (prover1 : Prover) (prover2 : Prover) : Prover =
        seq {
            yield prover1
            yield prover2
        } |> serial
