﻿namespace Bernsrite.Flogic

/// A language to reason about.
type Language =
    {
        /// Constants of the langugage. E.g. "0".
        Constants : Constant[]

        /// Functions of the language. E.g. s(x).
        Functions : Function[]

        /// Predicates of the language. E.g. "P(x, y)".
        Predicates : Predicate[]

        /// Parser for this language.
        Parser : Parser<Formula>
    }

module Language =

    /// The default empty language.
    let empty =
        {
            Constants = Array.empty
            Functions = Array.empty
            Predicates = Array.empty
            Parser = (fun _ -> failwith "No parser")
        }

    /// Creates a language.
    let create constants functions predicates =
        {
            Constants = constants
            Functions = functions
            Predicates = predicates
            Parser =
                constants
                    |> Array.map Constant.name
                    |> Parser.makeParser
        }

    /// Parses the given string using the given language.
    let parse language str =
        let formula = Parser.run language.Parser str
        let undeclaredFunctions =
            let functions =
                formula
                    |> Formula.getFunctions
                    |> Map.keys
            Set.difference functions (set language.Functions)
        let undeclaredPredicates =
            let predicates =
                formula
                    |> Formula.getPredicates
                    |> Map.keys
            Set.difference predicates (set language.Predicates)
        if undeclaredFunctions.IsEmpty then
            if undeclaredPredicates.IsEmpty then
                formula
            else
                failwithf "Undeclared predicates: %A" undeclaredPredicates
        else
            failwithf "Undeclared functions: %A" undeclaredFunctions
