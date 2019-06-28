namespace Discover

open System

/// Based on the syntax of first-order logic. This is also isomorphic to
/// Stanford's relational/Herbrand logic syntax:
///    +--------------------------+------------------------------------+
///    | Stanford                 | First-order                        |
///    +--------------------------+------------------------------------+
///    | Relational logic         |                                    |
///    |    Object constant       | Function of arity 0                |
///    |    Variable              | Variable                           |
///    |    Relation constant     | Predicate                          |
///    |    Term                  | Term                               |
///    |    Relational sentence   | Atomic formula                     |
///    |    Logical sentence      | Non-atomic, non-quantified formula |
///    |    Quantified sentence   | Quantified formula                 |
///    | Herbrand logic           |                                    |
///    |    Function constant     | Function of arity > 0              |
///    |    Functional expression | Function application               |
///    +--------------------------+------------------------------------+
/// See http://intrologic.stanford.edu/public/index.php

/// E.g. Mortal(x) is a predicate of arity 1.
type Predicate = Predicate of name : string * arity : int

/// E.g. Man(Socrates) -> Mortal(Socrates).
[<StructuredFormatDisplay("{String}")>]
type Formula =

    /// Atomic formula (no sub-formulas): P(t1, t2, ...)
    | Formula of Predicate * Term[]

    /// Negation: ~P
    | Not of Formula

    /// Conjunction: P & Q
    | And of Formula * Formula

    /// Disjunction: P | Q
    | Or of Formula * Formula

    /// Implication: P -> Q
    | Implication of Formula * Formula

    /// Biconditional: P <-> Q
    | Biconditional of Formula * Formula

    /// Existential quantifier: ∃x.P(x)
    | Exists of Variable * Formula

    /// Universal quantifier: ∀x.P(x)
    | ForAll of Variable * Formula

    /// Display string.
    member this.String =

        let rec loop isRoot =

            let infix symbol formula1 formula2 =
                sprintf "%s%s %s %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    symbol
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")

            function
                | Formula (Predicate (name, arity), terms) ->
                    if (arity <> terms.Length) then
                        failwith "Arity mismatch"
                    if arity = 0 then name
                    else
                        sprintf "%s(%s)" name <| String.Join(", ", terms)
                | Not formula ->
                    sprintf "~%s" (formula |> loop false)
                | And (formula1, formula2) ->
                    infix "&" formula1 formula2
                | Or (formula1, formula2) ->
                    infix "|" formula1 formula2
                | Implication (formula1, formula2) ->
                    infix "⇒" formula1 formula2
                | Biconditional (formula1, formula2) ->
                    infix "⇔" formula1 formula2
                | Exists (Variable variable, formula) ->
                    sprintf "∃%s.%s"
                        variable
                        (formula |> loop false)
                | ForAll (Variable variable, formula) ->
                    sprintf "∀%s.%s"
                        variable
                        (formula |> loop false)

        this |> loop true

    /// Display string.
    override this.ToString() =
        this.String

module Formula =

    /// Display string.
    let toString (formula : Formula) =
        formula.ToString()

    /// Tries to substitute the given term for the given variable in the given
    /// formula. Fails if this would capture any of the variables in the given
    /// term.
    /// See https://math.stackexchange.com/questions/3272333/restrictions-on-existential-introduction-in-first-order-logic
    let trySubstitute variable term formula =

            // variables that must avoid capture
        let termVariables =
            term |> Term.getVariables

            // substitutes within a term
        let rec substituteTerm = function
            | Term var as oldTerm ->
                if var = variable then term
                else oldTerm
            | Application (func, oldTerms) ->
                Application (
                    func,
                    oldTerms |> substituteTerms)

            // substitutes within multiple terms
        and substituteTerms oldTerms =
            oldTerms |> Array.map substituteTerm

        let rec loop formula =

                // substitutes within a unary formula
            let unary formula constructor =
                opt {
                    let! formula' = loop formula
                    return constructor formula'
                }

                // substitutes within a binary formula
            let binary formula1 formula2 constructor =
                opt {
                    let! formula1' = loop formula1
                    let! formula2' = loop formula2
                    return constructor (formula1', formula2')
                }

                // substitutes within a quantified formula
            let quantified oldVariable formula constructor =
                if termVariables.Contains(oldVariable) then
                    None
                else opt {
                    if variable = oldVariable then
                        return constructor (oldVariable, formula)
                    else
                        return! unary formula (fun formula' ->
                            constructor (oldVariable, formula'))
                }

                // substitutes within a formula
            match formula with
                | Formula (predicate, oldTerms) ->
                    Formula (
                        predicate,
                        oldTerms |> substituteTerms)
                        |> Some
                | Not formula ->
                    Not |> unary formula
                | And (formula1, formula2) ->
                    And |> binary formula1 formula2
                | Or (formula1, formula2) ->
                    Or |> binary formula1 formula2
                | Implication (formula1, formula2) ->
                    Implication |> binary formula1 formula2
                | Biconditional (formula1, formula2) ->
                    Biconditional |> binary formula1 formula2
                | Exists (oldVariable, formula) ->
                    Exists |> quantified oldVariable formula
                | ForAll (oldVariable, formula) ->
                    ForAll |> quantified oldVariable formula

        loop formula

    /// Substitutes one term for another in the given formula in all possible ways.
    /// Does not attempt to avoid variable capture.
    let substitute oldTerm newTerm formula =

            // substitutes within a variable
        let substituteVariable variable =
            seq {
                match oldTerm, newTerm with
                    | (Term oldVariable, Term newVariable) ->
                        if variable = oldVariable then
                            yield newVariable
                    | _ -> ()
                yield variable
            }

            // substitutes within a term
        let rec substituteTerm term =
            seq {
                if term = oldTerm then
                    yield newTerm
                else
                    match term with
                        | Application (func, terms) ->
                            for newTerms in terms |> substituteTerms do
                                yield Application (func, newTerms)
                        | _ -> ()
                yield term
            }

            // substitutes within multiple terms
        and substituteTerms terms =
            terms
                |> Seq.map (substituteTerm >> Seq.toList)
                |> Seq.toList
                |> List.cartesian
                |> Seq.map Seq.toArray

            // substitutes within a formula
        let rec loop formula =

                // substitutes within a binary formula
            let binary formula1 formula2 constructor =
                seq {
                    for formula1' in loop formula1 do
                        for formula2' in loop formula2 do
                            yield constructor (formula1', formula2')
                }

                // substitutes within a quantified formula
            let quantified variable formula constructor =
                seq {
                    for variable' in substituteVariable variable do
                        for formula' in loop formula do
                            yield constructor (variable', formula')
                }

            seq {
                match formula with
                    | Formula (predicate, terms) ->
                        for newTerms in terms |> substituteTerms do
                            yield Formula (predicate, newTerms)
                    | Not formula ->
                        for formula' in loop formula do
                            yield Not formula'
                    | And (formula1, formula2) ->
                        yield! And |> binary formula1 formula2
                    | Or (formula1, formula2) ->
                        yield! Or |> binary formula1 formula2
                    | Implication (formula1, formula2) ->
                        yield! Implication |> binary formula1 formula2
                    | Biconditional (formula1, formula2) ->
                        yield! Biconditional |> binary formula1 formula2
                    | Exists (variable, formula) ->
                        yield! Exists |> quantified variable formula
                    | ForAll (variable, formula) ->
                        yield! ForAll |> quantified variable formula
            }

        [|
            for formula' in loop formula do
                if newTerm = oldTerm || formula' <> formula then
                    yield formula'
        |]

    /// Answers the free variables in the given formula.
    let getFreeVariables formula =

        let rec loop formula =
            seq {
                match formula with
                    | Formula (_, terms) ->
                        for term in terms do
                            yield! term |> Term.getVariables
                    | Not formula ->
                        yield! formula |> loop
                    | And (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Or (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Implication (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Biconditional (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Exists (variable, formula) ->
                        for var in formula |> loop do
                            if var <> variable then
                                yield var
                    | ForAll (variable, formula) ->
                        for var in formula |> loop do
                            if var <> variable then
                                yield var
            }

        formula
            |> loop
            |> set

    /// Indicates whether the given variable occurs free within the given
    /// formula.
    let isFree variable formula =
        formula
            |> getFreeVariables
            |> Set.contains variable

    /// http://t0yv0.blogspot.com/2011/09/transforming-large-unions-in-f.html
    let transform func =
        let (!) = func
        function
            | Formula _ as fla -> fla
            | Not fla -> Not (!fla)
            | And (fla1, fla2) -> And (!fla1, !fla2)
            | Or (fla1, fla2) -> Or (!fla1, !fla2)
            | Implication (fla1, fla2) -> Implication (!fla1, !fla2)
            | Biconditional (fla1, fla2) -> Biconditional (!fla1, !fla2)
            | Exists (variable, fla) -> Exists (variable, !fla)
            | ForAll (variable, fla) -> ForAll (variable, !fla)
