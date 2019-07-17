namespace Bernsrite.Flogic

/// Clauses that are known/assumed true.
type Database =
    {
        /// Clauses are sorted by symbol count, so smaller clauses are enumerated
        /// first. This is the "least symbol count" heuristic.
        /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/GeneralHeuristics.shtml
        Clauses : Set<Clause>
    }

module Database =

    let create clauses =
        {
            Clauses = set clauses
        }
    
    let add clause database =
        {
            Clauses = database.Clauses.Add(clause)
        }
