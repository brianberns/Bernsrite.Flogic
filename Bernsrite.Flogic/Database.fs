namespace Bernsrite.Flogic

open System.Collections.Generic
open System.Collections.Immutable

/// Clauses that are known/assumed true.
type Database =
    {
        /// Clauses are sorted by symbol count, so smaller clauses are enumerated
        /// first. This is the "least symbol count" heuristic.
        /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/GeneralHeuristics.shtml
        ClauseMap : Map<(bool * Predicate), ImmutableSortedSet<Clause>>
    }

module Database =

    let clauseComparer =
        {
            new IComparer<Clause> with
                member __.Compare(clause1, clause2) =
                    match compare clause1.SymbolCount clause2.SymbolCount with
                        | 0 -> compare clause1 clause2
                        | result -> result
        }

    let empty =
        { ClauseMap = Map.empty }

    let private emptyBucket =
        ImmutableSortedSet.Create<Clause>(clauseComparer)
    
    let private getDistinctKeys clause =
        clause.Literals
            |> Seq.map (fun literal ->
                literal.IsPositive, literal.Predicate)
            |> Seq.distinct

    let add clause database =
        {
            ClauseMap =
                (database.ClauseMap, getDistinctKeys clause)
                    ||> Seq.fold (fun acc key ->
                        let clauses =
                            acc
                                |> Map.tryFind key
                                |> Option.defaultValue emptyBucket
                        acc.Add(key, clauses.Add(clause)))
        }

    let create clauses =
        (empty, clauses)
            ||> Seq.fold (fun acc clause ->
                acc |> add clause)

    let getPossibleResolutionClauses clause database =
        clause
            |> getDistinctKeys
            |> Seq.collect (fun (isPositive, predicate) ->
                database.ClauseMap
                    |> Map.tryFind (not isPositive, predicate)
                    |> Option.defaultValue emptyBucket)
