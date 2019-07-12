namespace Bernsrite.Flogic

[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Premises : Formula[]
        Goal : Formula
        Evidence : obj
    }
        
    /// Display string.
    member this.String =
        seq {
            yield "Premises:"
            for premise in this.Premises do
                yield sprintf "   %A" premise
            yield sprintf "Goal: %A" this.Goal
            yield sprintf "%A" this.Evidence
        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

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
