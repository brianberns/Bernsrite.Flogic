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
    | Variable of Name
    | Application of Function * List<Term>

    member this.String =
        match this with
            | Variable name -> name
            | Application ((Function (name, arity)), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)

    override this.ToString() =
        this.String

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
