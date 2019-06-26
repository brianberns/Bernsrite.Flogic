namespace Discover

open System
open FParsec

/// Shorthand for parser type.
type Parser<'t> = Parser<'t, unit>

module Parser =

    let special = set "(,)~&|<->∃∀."

    let isSpecial c =
        special.Contains(c)
            || Char.IsWhiteSpace(c)

    let parseName =
        many1Satisfy (isSpecial >> not)

    let parseVariable =
        parseName |>> Variable

    let parseTerm, parseTermRef =
        createParserForwardedToRef<Term, unit>()

    let parseTerms =
        spaces
            >>. skipChar '('
            >>. sepBy1 parseTerm (skipChar ',' .>> spaces)
            .>> skipChar ')'
            |>> Seq.toArray

    let parseApplication =
        pipe2 parseName parseTerms
            (fun name (terms : _[]) ->
                Application (Function (name, terms.Length), terms))

    let parseTermActual =
        attempt parseApplication
            <|> (parseVariable |>> Term)

    /// Runs the given parser on the given string.
    let run parser str =
        let parser = parser .>> eof   // force consumption of entire string
        match run parser str with
            | Success (result, _, _) -> result
            | Failure (msg, _, _) -> failwith msg

    do
        parseTermRef := parseTermActual
