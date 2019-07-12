namespace Bernsrite.Flogic

open System

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

type IEvidence =
    abstract member ToString : int -> string

[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Premises : Formula[]
        Goal : Formula
        Evidence : IEvidence
    }

    /// Display string.
    member this.ToString(level) =
        seq {

            yield "" |> Print.indent level
            yield "Premises:" |> Print.indent level
            for premise in this.Premises do
                yield premise |> Print.indent (level + 1)

            yield "" |> Print.indent level
            yield sprintf "Goal: %A" this.Goal |> Print.indent level

            yield this.Evidence.ToString(level + 1)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module Proof =

    let create premises goal evidence =
        {
            Premises = premises |> Seq.toArray
            Goal = goal
            Evidence = evidence
        }

type Prover = seq<Formula> (*premises*) -> Formula (*goal*) -> Option<Proof>

module Prover =

    /// Combines the given provers in series.
    let combine (prover1 : Prover) (prover2 : Prover) : Prover =
        fun premises goal ->
            prover1 premises goal
                |> Option.orElseWith (fun () ->
                    prover2 premises goal)

    /// Creates a serial prover from the given provers.
    let serial provers : Prover =
        fun premises goal ->
            provers
                |> Seq.tryPick (fun (prover : Prover) ->
                    prover premises goal)
