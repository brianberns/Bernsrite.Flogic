namespace Bernsrite.Flogic

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

    /// Symbols with special meanings.
    let symbols = set "-&(),.|~<>∀∃∧∨→⇒⊃⇐⇔¬!"

    /// Parses a name, such as "P" or "harry".
    let parseName =
        let isTerminator c =
            symbols.Contains(c)
                || Char.IsWhiteSpace(c)
        many1Satisfy (isTerminator >> not)

    /// Parses a variable.
    let parseVariable =
        parseName |>> Variable.create

    /// Skips any of the given strings.
    let skipAnyOfStr strs : Parser<_> =
        strs
            |> Seq.map skipString
            |> Seq.toList
            |> choice

    /// Skips surrounding parentheses.
    let parseParenthesized parser =
        skipChar '('
            >>. parser
            .>> skipChar ')'

    /// Makes parsers that recognize the given names as constants.
    let makeParsers constantNames =

        /// Parses a constant.
        let parseConstant =
            let constantsSet = set constantNames
            parse {
                let! name = parseName
                if constantsSet.Contains(name) then
                    return Constant.create name
            }

        /// Parses a term recursively.
        let parseTerm, parseTermRef =
            createParserForwardedToRef<Term, unit>()

        /// Parses a (potentially empty) list of terms.
        let parseTerms allowEmpty =
            let parsePresent =
                spaces
                    >>. parseParenthesized (
                        sepBy1 parseTerm (skipChar ',' .>> spaces))
                    |>> Seq.toArray
            if allowEmpty then
                attempt parsePresent
                    <|> preturn Array.empty
            else
                parsePresent

        /// Parses a function application term.
        let parseApplication =
            pipe2 parseName (parseTerms false)
                (fun name (terms : _[]) ->
                    Application (
                        Function.create name terms.Length,
                        terms))

        /// Parses a term.
        let parseTermActual =
            attempt parseApplication
                <|> attempt (parseConstant |>> ConstantTerm)
                <|> (parseVariable |>> VariableTerm)
        parseTermRef := parseTermActual

        /// Parses an atomic formula.
        let parseAtomic =
            pipe2 parseName (parseTerms true)
                (fun name (terms : _[]) ->
                    Atom ((Predicate.create name terms.Length), terms))

        /// Parses a formula recursively.
        let parseFormula, parseFormulaRef =
            createParserForwardedToRef<Formula, unit>()

        /// Parses a negation formula.
        let parseNot =
            skipAnyOf ['~'; '¬'; '!']
                >>. parseFormula
                |>> Not

        /// Parses a binary formula.
        let parseBinary : Parser<_> =
            [
                ["&"; "∧"], And
                ["|"; "∨"], Or
                ["->"; "=>"; "→"; "⇒"; "⊃"], Implication
                ["<-"; "<="; "⇐"], (fun (q, p) -> Implication (p, q))
                ["<->"; "<=>"; "⇔"], Biconditional
            ]
                |> Seq.map (fun (ops, constructor) ->
                    attempt (pipe3
                        parseFormula
                        (spaces >>. skipAnyOfStr ops .>> spaces)
                        parseFormula
                        (fun formula1 _ formula2 ->
                            constructor (formula1, formula2))))
                |> choice

        /// Parses a quantified formula.
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

        /// Parses a formula.
        /// https://stackoverflow.com/questions/56779430/parser-combinator-for-propositional-logic
        let parseFormulaActual =
            choice [
                attempt parseAtomic
                attempt parseNot
                attempt (parseParenthesized parseBinary)   // require parens to avoid left-recursion
                attempt parseQuantified
            ]
        parseFormulaRef := parseFormulaActual

        parseTerm, parseFormula

    /// Makes a formula parser that recognizes the given names as constants.
    let makeParser constantNames =
        let _, parseFormula = makeParsers constantNames
        parseFormula

    /// Runs the given parser on the given string.
    let run parser str =
        let parser = parser .>> eof   // force consumption of entire string
        match run parser str with
            | Success (result, _, _) -> result
            | Failure (msg, _, _) -> failwith msg
