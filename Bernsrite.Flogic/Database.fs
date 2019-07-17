namespace Bernsrite.Flogic

/// Clauses that are known/assumed true.
type Database =
    {
        Clauses : List<Clause>
    }

module Database =

    let create clauses =
        {
            Clauses = clauses |> Seq.toList
        }
    
    let add clause database =
        {
            Clauses = clause :: database.Clauses
        }
