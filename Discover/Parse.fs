namespace Discover

open System
open FParsec

/// Shorthand for parser type.
type Parser<'t> = Parser<'t, unit>

module Parser =

#if DEBUG
    let (<!>) (p: Parser<_,_>) label : Parser<_,_> =
        fun stream ->
            printfn "%A: Entering %s" stream.Position label
            let reply = p stream
            printfn "%A: Leaving %s (%A)" stream.Position label reply.Status
            reply
#endif

    let special = set "(,)~&|<->∃∀.∧¬"

    let isSpecial c =
        special.Contains(c)
            || Char.IsWhiteSpace(c)

    let parseName =
        many1Satisfy (isSpecial >> not)

    let parseVariable =
        parseName |>> Variable

    let parseTerm, parseTermRef =
        createParserForwardedToRef<Term, unit>()

    let parseTerms allowEmpty =
        let parsePresent =
            spaces
                >>. skipChar '('
                >>. sepBy1 parseTerm (skipChar ',' .>> spaces)
                .>> skipChar ')'
                |>> Seq.toArray
        if allowEmpty then
            attempt parsePresent
                <|> preturn Array.empty
        else
            parsePresent

    let parseApplication =
        pipe2 parseName (parseTerms false)
            (fun name (terms : _[]) ->
                Application (Function (name, terms.Length), terms))

    let parseFormula, parseFormulaRef =
        createParserForwardedToRef<Formula, unit>()

    let skipAnyOfStr strs =
        strs
            |> Seq.map skipString
            |> Seq.toList
            |> choice

    let parseParenthesized parser =
        skipChar '('
            >>. parser
            .>> skipChar ')'

    let makeParser constants : Parser<_> =

        let parseConstant =
            let constantsSet = set constants
            parse {
                let! name = parseName
                if constantsSet.Contains(name) then
                    return Term.constant name
            }

        let parseTermActual =
            attempt parseApplication
                <|> attempt parseConstant
                <|> (parseVariable |>> Term)

        parseTermRef := parseTermActual

        let parseAtomic =
            pipe2 parseName (parseTerms true)
                (fun name (terms : _[]) ->
                    Formula (Predicate (name, terms.Length), terms))
                        
        let parseNot =
            skipAnyOf ['~'; '¬'; '!']
                >>. parseFormula
                |>> Not

        let parseBinary : Parser<_> =
            [
                ["&"; "∧"], And
                ["|"; "∨"], Or
                ["->"; "=>"], Implication
                ["<->"; "<=>"], Biconditional
            ]
                |> Seq.map (fun (ops, constructor) ->
                    attempt (pipe3
                        parseFormula
                        (spaces >>. skipAnyOfStr ops .>> spaces)
                        parseFormula
                        (fun formula1 _ formula2 ->
                            constructor (formula1, formula2))))
                |> choice

        let parseQuantified =
            [
                '∃', Exists
                '∀', ForAll
            ]
                |> Seq.map (fun (op, constructor) ->
                    attempt (pipe4
                        (skipChar op)
                        parseVariable
                        (skipChar '.')
                        parseFormula
                        (fun _ variable _ formula ->
                            constructor (variable, formula))))
                |> choice

        let parseComplex =
            choice [
                attempt parseNot
                attempt (parseParenthesized parseBinary)
                attempt parseQuantified
            ]

        let parseFormulaActual =
            choice [
                attempt parseAtomic
                attempt parseComplex
            ]

        parseFormulaRef := parseFormulaActual
        parseFormulaActual

    /// Runs the given parser on the given string.
    let run parser str =
        let parser = parser .>> eof   // force consumption of entire string
        match run parser str with
            | Success (result, _, _) -> result
            | Failure (msg, _, _) -> failwith msg
