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
    | Formula of Predicate * List<Term>

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

        let rec loop isRoot formula =

            let infix symbol formula1 formula2 =
                sprintf "%s%s %s %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    symbol
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")

            match formula with
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

    /// Answers the distinct variables contained in the given formula.
    let getVariables formula =

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
                        yield variable
                        yield! formula |> loop
                    | ForAll (variable, formula) ->
                        yield variable
                        yield! formula |> loop
            }

        formula
            |> loop
            |> set

    /// Tries to substitute the given term for the given variable in the
    /// given formula.
    let trySubstitute variable term formula =

            // extract variables from given term
        let newVariables = term |> Term.getVariables

            // substitutes within a term
        let rec substituteTerm = function
            | Term var as oldTerm ->
                assert(newVariables.Contains(var) |> not)
                if var = variable then term
                else oldTerm
            | Application (func, oldTerms) ->
                Application (
                    func,
                    oldTerms |> substituteTerms)

            // substitutes within multiple terms
        and substituteTerms oldTerms =
            oldTerms
                |> List.map substituteTerm

            // substitutes within a formula
        let rec substitute = function
            | Formula (predicate, oldTerms) ->
                Formula (
                    predicate,
                    oldTerms |> substituteTerms)
            | Not formula ->
                Not (
                    formula |> substitute)
            | And (formula1, formula2) ->
                And (
                    formula1 |> substitute,
                    formula2 |> substitute)
            | Or (formula1, formula2) ->
                Or (
                    formula1 |> substitute,
                    formula2 |> substitute)
            | Implication (formula1, formula2) ->
                Implication (
                    formula1 |> substitute,
                    formula2 |> substitute)
            | Biconditional (formula1, formula2) ->
                Biconditional (
                    formula1 |> substitute,
                    formula2 |> substitute)
            | Exists (variable, formula) ->
                Exists (
                    variable,
                    formula |> substitute)
            | ForAll (variable, formula) ->
                ForAll (
                    variable,
                    formula |> substitute)

            // ensure substitution is valid before doing it
        let overlap =
            let oldVariables = formula |> getVariables
            Set.intersect newVariables oldVariables
        if overlap.IsEmpty then
            formula |> substitute |> Some
        else
            None
