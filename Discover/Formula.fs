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

    /// Substitutes the given term for the given variable in the
    /// given formula.
    let substitute variable term formula =

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
            oldTerms
                |> List.map substituteTerm

            // substitutes within a formula
        let rec loop = function
            | Formula (predicate, oldTerms) ->
                Formula (
                    predicate,
                    oldTerms |> substituteTerms)
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
                    variable,
                    formula |> loop)
            | ForAll (variable, formula) ->
                ForAll (
                    variable,
                    formula |> loop)

        formula |> loop

    /// Indicates whether the given variable occurs free within the
    /// given formula.
    let isFree variable formula =

        let rec loop = function
            | Formula (_, terms) ->
                let contains =
                    Term.getVariables >> Set.contains variable
                terms |> Seq.exists contains
            | Not formula ->
                formula |> loop
            | And (formula1, formula2) ->
                (formula1 |> loop) || (formula2 |> loop)
            | Or (formula1, formula2) ->
                (formula1 |> loop) || (formula2 |> loop)
            | Implication (formula1, formula2) ->
                (formula1 |> loop) || (formula2 |> loop)
            | Biconditional (formula1, formula2) ->
                (formula1 |> loop) || (formula2 |> loop)
            | Exists (var, formula) ->
                if var = variable then false
                else formula |> loop
            | ForAll (var, formula) ->
                if var = variable then false
                else formula |> loop

        formula |> loop

    /// A term is free for a variable in a formula iff no free occurrence
    /// of the νariable occurs within the scope of a quantifier of some
    /// variable in the term.
    /// http://intrologic.stanford.edu/public/section.php?section=section_08_02
    let isFreeFor term variable formula =

        /// Answers the quantified variables in whose scope the given variable
        /// occurs free in the given formula.
        let getFreeScopes variable =

            let rec loop activeScopes formula =
                seq {
                    match formula with
                        | Formula (_, terms) ->
                            let contains =
                                Term.getVariables >> Set.contains variable
                            if terms |> Seq.exists contains then
                                yield! activeScopes
                        | Not formula ->
                            yield! formula |> loop activeScopes
                        | And (formula1, formula2) ->
                            yield! formula1 |> loop activeScopes
                            yield! formula2 |> loop activeScopes
                        | Or (formula1, formula2) ->
                            yield! formula1 |> loop activeScopes
                            yield! formula2 |> loop activeScopes
                        | Implication (formula1, formula2) ->
                            yield! formula1 |> loop activeScopes
                            yield! formula2 |> loop activeScopes
                        | Biconditional (formula1, formula2) ->
                            yield! formula1 |> loop activeScopes
                            yield! formula2 |> loop activeScopes
                        | Exists (var, formula) ->
                            if var <> variable then
                                let activeScopes' = var :: activeScopes
                                yield! formula |> loop activeScopes'
                        | ForAll (var, formula) ->
                            if var <> variable then
                                let activeScopes' = var :: activeScopes
                                yield! formula |> loop activeScopes'
                }

            formula
                |> loop List.empty
                |> set

        let variableScopes =
            variable |> getFreeScopes
        let termVariables =
            term |> Term.getVariables
        Set.intersect variableScopes termVariables
            |> Set.isEmpty
