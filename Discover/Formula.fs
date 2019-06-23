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

    /// Substitutes one term for another in the given formula.
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
        | ForAll (variable, formula)
            when formula |> isFreeFor term variable ->
                formula
                    |> substitute (Term variable) term
                    |> Some
        | _ -> None

    /// Tries to eliminate an existential quantification.
    let tryExistentialElimination = function
        | Exists (variable, formula) ->
            let skolem =
                formula
                    |> getFreeVariables
                    |> Seq.toArray
                    |> Skolem.createTerm
            formula
                |> substitute (Term variable) skolem
                |> Some
        | _ -> None
