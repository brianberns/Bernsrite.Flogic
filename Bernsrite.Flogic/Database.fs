namespace Bernsrite.Flogic

open System
open System.Collections.Generic
open System.Collections.Immutable

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

[<StructuredFormatDisplay("{Name}")>]
type RoleTag =
    | Tag of string

    /// Display string.
    member this.Name =
        let (Tag name) = this
        name

    /// Display string.
    override this.ToString() =
        this.Name

/// Clauses that are known/assumed true.
[<StructuredFormatDisplay("{String}")>]
type Database =
    {
        /// Clauses are sorted by symbol count, so smaller clauses are enumerated
        /// first. This is the "least symbol count" heuristic.
        /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/GeneralHeuristics.shtml
        ClauseMap : Map<RoleTag, ImmutableSortedSet<Clause>>
    }

    /// Display string.
    member this.ToString(level) =
        seq {
            yield ""
            yield "Database:" |> Print.indent level
            for tag, clauses in this.ClauseMap |> Map.toSeq do
                yield sprintf "%As:" tag |> Print.indent (level + 1)
                for clause in clauses do
                    yield clause |> Print.indent (level + 2)
        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module ImmutableSortedSet =

    let add value (set : ImmutableSortedSet<_>) =
        set.Add(value)

module Database =

    let clauseComparer =
        {
            new IComparer<Clause> with
                member __.Compare(clause1, clause2) =
                    match compare clause1.SymbolCount clause2.SymbolCount with
                        | 0 -> compare clause1 clause2
                        | result -> result
        }

    let private emptyBucket =
        ImmutableSortedSet.Create<Clause>(clauseComparer)

    let empty =
        { ClauseMap = Map.empty }

    let add clause tag database =
        {
            ClauseMap =
                let bucket =
                    database.ClauseMap
                        |> Map.tryFind tag
                        |> Option.defaultValue emptyBucket
                        |> ImmutableSortedSet.add clause
                database.ClauseMap
                    |> Map.add tag bucket
        }

    let create taggedClauses =
        (empty, taggedClauses)
            ||> Seq.fold (fun acc (clause, tag) ->
                acc |> add clause tag)

    let getPossibleResolutionClauses clause tag database =
        let preferredTag = tag
        (*
            match tag with
                | "GoalClause" -> "InductionClause"
                | _ -> tag
        *)
        [|
            yield! database.ClauseMap.[preferredTag]
            for otherTag, clauses in database.ClauseMap |> Map.toSeq do
                if otherTag <> preferredTag then
                    yield! clauses
        |]
