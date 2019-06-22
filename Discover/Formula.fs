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

type Arity = uint32
type Name = string

type Function = Function of Name * Arity
type Variable = Variable of Name

/// A term typically denotes an object that exists in the world.
/// E.g.
///    * Joe: constant (i.e. function of arity 0)
///    * Joe's father: function application
///    * someone: variable
[<StructuredFormatDisplay("{String")>]
type Term =
    | Term of Variable
    | Application of Function * List<Term>

    member this.String =
        match this with
            | Term (Variable name) -> name
            | Application ((Function (name, arity)), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)

    override this.ToString() =
        this.String

module Term =

    /// Answers the distinct variables contained in the given term.
    let getVariables term =

        let rec loop term =
            seq {
                match term with
                    | Term var -> yield var
                    | Application (_, terms) ->
                        for term in terms do
                            yield! term |> loop
            }

        term
            |> loop
            |> set

/// E.g. Mortal(x) is a predicate of arity 1.
type Predicate = Predicate of Name * Arity

/// E.g. Man(Socrates) -> Mortal(Socrates).
[<StructuredFormatDisplay("{String}")>]
type Formula =

        // atomic (no sub-formulas)
    | Holds of Predicate * List<Term>
    | Equality of Term * Term

        // negation
    | Not of Formula

        // binary connectives
    | And of Formula * Formula
    | Or of Formula * Formula
    | Implication of Formula * Formula
    | Biconditional of Formula * Formula

        // quantifiers
    | Exists of Variable * Formula
    | ForAll of Variable * Formula

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
                | Holds (Predicate (name, arity), terms) ->
                    assert(arity = uint32 terms.Length)
                    if arity = 0u then name
                    else
                        sprintf "%s(%s)" name <| String.Join(", ", terms)
                | Equality (term1, term2) ->
                    sprintf "%A = %A" term1 term2
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
                | Exists (variable, formula) ->
                    sprintf "∃%A.%s"
                        variable
                        (formula |> loop false)
                | ForAll (variable, formula) ->
                    sprintf "∀%A.%s"
                        variable
                        (formula |> loop false)

        this |> loop true

    override this.ToString() =
        this.String

module Formula =

    /// Answers the distinct variables contained in the given formula.
    let getVariables formula =

        let rec loop formula =
            seq {
                match formula with
                    | Holds (_, terms) ->
                        for term in terms do
                            yield! term |> Term.getVariables
                    | Equality (term1, term2) ->
                        yield! term1 |> Term.getVariables
                        yield! term2 |> Term.getVariables
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

    let trySubstitute variable term formula =

        let newVariables = term |> Term.getVariables

        let rec substituteTerm = function
            | Term var as oldTerm ->
                assert(newVariables.Contains(var) |> not)
                if var = variable then term
                else oldTerm
            | Application (func, oldTerms) ->
                Application (
                    func,
                    oldTerms |> substituteTerms)

        and substituteTerms oldTerms =
            oldTerms
                |> List.map substituteTerm

        let rec substitute = function
            | Holds (predicate, oldTerms) ->
                Holds (
                    predicate,
                    oldTerms |> substituteTerms)
            | Equality (oldTerm1, oldTerm2) ->
                Equality (
                    oldTerm1 |> substituteTerm,
                    oldTerm2 |> substituteTerm)
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

        let oldVariables = formula |> getVariables
        if Set.intersect newVariables oldVariables |> Set.isEmpty then
            formula |> substitute |> Some
        else
            None
