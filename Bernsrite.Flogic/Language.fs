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

    let private getContents formula =

        let rec loopTerm functions = function
            | Application (func, terms) ->
                let functions' =
                    functions |> Set.add func
                loopTerms functions' terms
            | _ -> functions

        and loopTerms functions terms =
            Seq.fold loopTerm functions terms

        let rec loopPredicate functions predicates = function
            | Atom (predicate, terms) ->
                let functions' =
                    loopTerms functions terms
                        |> Set.union functions
                let predicates' =
                    predicates |> Set.add predicate
                functions', predicates'
            | Not formula
            | Exists (_, formula)
            | ForAll (_, formula) ->
                formula |> loopPredicate functions predicates
            | And (formula1, formula2)
            | Or (formula1, formula2)
            | Implication (formula1, formula2)
            | Biconditional (formula1, formula2) ->
                let functions', predicates' =
                    formula1 |> loopPredicate functions predicates
                formula2 |> loopPredicate functions' predicates'

        formula |> loopPredicate Set.empty Set.empty
                
    let parse language str =
        let parser = makeParser language
        let formula = Parser.run parser str
        let functions, predicates = getContents formula
        let undeclaredFunctions =
            Set.difference functions (set language.Functions)
        let undeclaredPredicates =
            Set.difference predicates (set language.Predicates)
        if undeclaredFunctions.IsEmpty then
            if undeclaredPredicates.IsEmpty then
                formula
            else
                failwithf "Undeclared predicates: %A" undeclaredPredicates
        else
            failwithf "Undeclared functions: %A" undeclaredFunctions
