namespace Bernsrite.Flogic

/// A language to reason about.
type Language =
    {
        /// Constants of the langugage. E.g. "0".
        Constants : Constant[]

        /// Functions of the language. E.g. s(x).
        Functions : Function[]

        /// Predicates of the language. E.g. "equal(x, y)".
        Predicates : Predicate[]
    }

module Language =

    /// Creates a parser for the given language.
    let makeParser language : Parser<_> =
        language.Constants
            |> Array.map (fun (Constant name) -> name)
            |> Parser.makeParser
