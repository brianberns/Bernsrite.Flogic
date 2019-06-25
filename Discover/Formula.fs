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
type Predicate = Predicate of Name * Arity

/// E.g. Man(Socrates) -> Mortal(Socrates).
[<StructuredFormatDisplay("{String}")>]
type Formula =

    /// Atomic formula (no sub-formulas): P(t1, t2, ...)
    | Formula of Predicate * Term[]

    // Negation: ~P
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
                    assert(arity = uint32 terms.Length)
                    if arity = 0u then name
                    else
                        sprintf "%s(%s)" name <| String.Join(", ", terms)
                | Not formula ->
                    sprintf "~%A" formula
                | And (formula1, formula2) ->
                    infix "&" formula1 formula2
                | Or (formula1, formula2) ->
                    infix "|" formula1 formula2
                | Implication (formula1, formula2) ->
                    infix "->" formula1 formula2
                | Biconditional (formula1, formula2) ->
                    infix "<->" formula1 formula2
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

    /// https://stackoverflow.com/questions/7818277/is-there-a-standard-option-workflow-in-f
    type OptionBuilder() =
        member __.Bind(v, f) = Option.bind f v
        member __.Return(v) = Some v
        member __.ReturnFrom(o) = o
        member __.Zero() = None

    let option = OptionBuilder()

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

            // substitutes within a formula
        let rec loop = function
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

            // substitutes within a unary formula
        and unary formula constructor =
            option {
                let! formula' = loop formula
                return constructor formula'
            }

            // substitutes within a binary formula
        and binary formula1 formula2 constructor =
            option {
                let! formula1' = loop formula1
                let! formula2' = loop formula2
                return constructor (formula1', formula2')
            }

            // substitutes within a quantified formula
        and quantified oldVariable formula constructor =
            if termVariables.Contains(oldVariable) then
                None
            else option {
                if variable = oldVariable then
                    return constructor (oldVariable, formula)
                else
                    return! unary formula (fun formula' ->
                        constructor (oldVariable, formula'))
            }

        formula |> loop

    /// Substitutes one term for another in the given formula. Does not attempt
    /// to avoid variable capture.
    let substitute oldTerm newTerm formula =

            // substitutes within a variable
        let substituteVariable variable =
            match oldTerm, newTerm with
                | (Term oldVariable, Term newVariable) ->
                    if variable = oldVariable then newVariable
                    else variable
                | _ -> variable

            // substitutes within a term
        let rec substituteTerm term =
            if term = oldTerm then newTerm
            else
                match term with
                    | Term _ -> term
                    | Application (func, terms) ->
                        Application (
                            func,
                            terms |> substituteTerms)

            // substitutes within multiple terms
        and substituteTerms terms =
            terms |> Array.map substituteTerm

            // substitutes within a formula
        let rec loop = function
            | Formula (predicate, terms) ->
                Formula (
                    predicate,
                    terms |> substituteTerms)
            | Not formula ->
                Not (
                    formula |> loop)
            | And (formula1, formula2) ->
                And (
                    formula1 |> loop,
                    formula2 |> loop)
            | Or (formula1, formula2) ->
                Or (
                    formula1 |> loop,
                    formula2 |> loop)
            | Implication (formula1, formula2) ->
                Implication (
                    formula1 |> loop,
                    formula2 |> loop)
            | Biconditional (formula1, formula2) ->
                Biconditional (
                    formula1 |> loop,
                    formula2 |> loop)
            | Exists (variable, formula) ->
                Exists (
                    substituteVariable variable,
                    formula |> loop)
            | ForAll (variable, formula) ->
                ForAll (
                    substituteVariable variable,
                    formula |> loop)

        formula |> loop

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

    /// Tries to introduce a universal quantification of the given formula.
    let tryUniversalIntroduction variable assumptions formula =
        let isValid =
            if formula |> isFree variable then
                assumptions
                    |> Seq.forall (
                        isFree variable >> not)
            else true
        if isValid then
            ForAll (variable, formula) |> Some
        else None

    /// Tries to instantiate a universal quantification.
    let tryUniversalElimination term = function
        | ForAll (variable, formula) ->
            formula |> trySubstitute variable term
        | _ -> None

    /// Tries to introduce an existential quantification of the given formula.
    let tryExistentialIntroduction term variable formula =
        option {
            let formula' =
                formula |> substitute term (Term variable)
            let! formula'' =
                formula' |> trySubstitute variable term
            if formula'' = formula then
                return Exists (variable, formula')
        }

    /// Tries to eliminate an existential quantification using the given
    /// Skolem function.
    let tryExistentialElimination skolem = function
        | Exists (variable, inner) as formula ->
            let term =
                Application (
                    skolem,
                    formula
                        |> getFreeVariables
                        |> Seq.map Term
                        |> Seq.toArray)
            inner |> trySubstitute variable term
        | _ -> None
