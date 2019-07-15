namespace Bernsrite.Flogic

open System

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

/// Interface for pretty printing.
type Printable =
    {
        /// Full object.
        Object : obj

        /// Creates a string indented to the given level.
        ToString : int (*level, 0-based*) -> string
    }

/// Input to and output of a proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        /// Premises of this proof.
        Premises : Formula[]

        /// Goal of this proof.
        Goal : Formula

        /// Result of this proof: proved or disproved.
        Result : bool

        /// Derivation of this proof.
        Derivation : Printable
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

            yield ""
            yield if this.Result then "Proved" else "Disproved"
                |> Print.indent level

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module Proof =

    /// Creates a proof.
    let create premises goal result derivation =
        {
            Premises = premises |> Seq.toArray
            Goal = goal
            Result = result
            Derivation = derivation
        }
