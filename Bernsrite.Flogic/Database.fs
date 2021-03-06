﻿namespace Bernsrite.Flogic

/// Clauses that are known/assumed true.
[<StructuredFormatDisplay("{String}")>]
type Database =
    {
        /// Initial database contents.
        InitialClauses : Clause[]

        /// Clauses added to the database after creation.
        AddedClauses : List<Clause>
    }

    /// All clauses in this database, in order.
    member this.Clauses =
        Seq.append
            this.InitialClauses
            (this.AddedClauses |> List.rev)

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

    /// Initializes a database with the given clauses.
    let create clauses =
        {
            InitialClauses = clauses |> Seq.toArray
            AddedClauses = List.empty
        }

    /// Adds the given clause to the given database.
    let add clause database =
        {
            database with
                AddedClauses =
                    clause :: database.AddedClauses
        }
