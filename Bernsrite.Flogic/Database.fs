namespace Bernsrite.Flogic

open System.Collections.Generic
open System.Collections.Immutable

/// Clauses that are known/assumed true.
type Database =
    {
        /// Clauses are sorted by symbol count, so smaller clauses are enumerated
        /// first. This is the "least symbol count" heuristic.
        /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/GeneralHeuristics.shtml
        Clauses : ImmutableSortedSet<Clause>
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

    let create (clauses : _[]) =
        {
            Clauses = ImmutableSortedSet.Create(clauseComparer, clauses)
        }
    
    let add clause database =
        {
            Clauses = database.Clauses.Add(clause)
        }
