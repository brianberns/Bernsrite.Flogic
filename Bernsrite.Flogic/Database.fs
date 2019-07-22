namespace Bernsrite.Flogic

open System

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

[<RequireQualifiedAccess>]
type Tag =
    | Axiom
    | Premise
    | Induction
    | Goal
    | Step

/// Clauses that are known/assumed true.
[<StructuredFormatDisplay("{String}")>]
type Database =
    {
        InitialClauses : Clause[]
        AddedClauses : List<Clause>
    }

    member this.Clauses =
        seq {
            yield! this.InitialClauses
            yield! this.AddedClauses |> List.rev
        }

    /// Display string.
    member this.ToString(level) =
        seq {
            yield ""
            yield "Database:" |> Print.indent level
            for clause in this.Clauses do
                yield clause |> Print.indent (level + 1)
        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module Database =

    let create taggedClauses =
        {
            InitialClauses =
                taggedClauses
                    |> Seq.map fst
                    |> Seq.toArray
            AddedClauses = List.empty
        }

    let add clause database =
        {
            database with
                AddedClauses =
                    clause :: database.AddedClauses
        }

    let getPossibleResolutionClauses (clause : Clause) (database : Database) =
        database.Clauses
