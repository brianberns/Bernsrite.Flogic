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

type FormulaRole =
    | AxiomFormula
    | InductionFormula
    | GoalFormula

type ClauseRole =
    | AxiomClause
    | InductionClause
    // | InductionAntecedentClause
    // | InductionConsequentClause
    | GoalClause
    | StepClause

/// Clauses that are known/assumed true.
[<StructuredFormatDisplay("{String}")>]
type Database =
    {
        /// Clauses are sorted by symbol count, so smaller clauses are enumerated
        /// first. This is the "least symbol count" heuristic.
        /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/GeneralHeuristics.shtml
        ClauseMap : Map<ClauseRole, ImmutableSortedSet<Clause>>
    }

    /// Display string.
    member this.ToString(level) =
        seq {
            yield ""
            yield "Database:" |> Print.indent level
            for (role, clauses) in this.ClauseMap |> Map.toSeq do
                yield sprintf "%A:" role |> Print.indent (level + 1)
                for clause in clauses do
                    yield clause |> Print.indent (level + 2)
        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module Database =

    let clauseComparer isAscending =
        {
            new IComparer<Clause> with
                member __.Compare(clause1, clause2) =
                    match compare clause1.SymbolCount clause2.SymbolCount with
                        | 0 -> compare clause1 clause2
                        | result -> if isAscending then result else -result
        }

    let private emptyBucket isAscending =
        ImmutableSortedSet.Create<Clause>(clauseComparer isAscending)

    let empty =
        {
            ClauseMap =
                Map [
                    AxiomClause, emptyBucket true
                    // InductionAntecedentClause, emptyBucket false
                    // InductionConsequentClause, emptyBucket false
                    InductionClause, emptyBucket false
                    GoalClause, emptyBucket true
                    StepClause, emptyBucket true
                ]
        }

    let add clause role database =
        {
            ClauseMap =
                let bucket = database.ClauseMap.[role].Add(clause)
                database.ClauseMap
                    |> Map.add role bucket
        }

    let create annotatedClauses =
        (empty, annotatedClauses)
            ||> Seq.fold (fun acc (clause, role) ->
                acc |> add clause role)

    let getPossibleResolutionClauses role database =
        [|
            yield! database.ClauseMap.[role]
            for (role', clauses) in database.ClauseMap |> Map.toSeq do
                if role' <> role then
                    yield! clauses
        |]
