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

namespace Discover

open System

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

type Predicate = Predicate of Name * Arity   // produces a Boolean

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

type MetaVariable = Formula

module MetaVariable =

    /// Creates a metavariable. This is currently implemented as
    /// 0-arity placeholder for a predicate.
    let create name : MetaVariable =
        Holds (Predicate (name, 0u), [])

    let nameOf (metaVar : MetaVariable) =
        match metaVar with
            | Holds (Predicate (name, 0u), []) -> name
            | _ -> failwith "Unexpected"

/// A schema is a formula that might contain metavariables.
type Schema = Formula

/// Binding of metavariables to formulas.
type Binding = Map<MetaVariable, Formula>

module Schema =

    /// Finds possible mappings of the given formula to the given
    /// schema (including potentially contradictory ones).
    let private findMappingOpts formula schema =

        let rec loop formula (schema : Schema) =
            seq {
                match (formula, schema) with

                        // bind metavariable
                    | _, Holds (Predicate (_, 0u), terms) ->
                        assert(terms.Length = 0)
                        yield Some ((schema : MetaVariable), formula)

                        // recurse
                    | Not formula', Not schema' ->
                        yield! schema' |> loop formula'
                    | And (formula1, formula2), And (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Or (formula1, formula2), Or (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Implication (formula1, formula2), Implication (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Biconditional (formula1, formula2), Biconditional (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2

                        // error
                    | _ -> yield None
            }

        schema
            |> loop formula
            |> Seq.toArray

    /// Resolves errors or incompatibilities in the given mappings.
    let private resolve mappingOpts : Option<Binding> =

            // did an error occur?
        let mappings =
            mappingOpts |> Array.choose id
        assert(mappings.Length <= mappingOpts.Length)
        if mappings.Length = mappingOpts.Length then

                // validate mappings
            let distinct = mappings |> Array.distinct
            let isValid =
                distinct
                    |> Seq.groupBy fst
                    |> Seq.forall (fun (_, group) ->
                        (group |> Seq.length) = 1)

                // package mappings into a binding
            if isValid then
                let binding = distinct |> Map.ofSeq
                assert(binding.Count = distinct.Length)
                Some binding
            else None

        else None

    /// Finds all possible bindings of the given formulas to the
    /// given schemas.
    let bind formulas schemas =
        if Array.length formulas >= Array.length schemas then
            formulas
                |> List.ofArray
                |> List.permutations schemas.Length
                |> Seq.choose (fun formulaList ->
                    Seq.zip formulaList schemas
                        |> Seq.collect (fun (formula, schema) ->
                            schema |> findMappingOpts formula)
                        |> Seq.toArray
                        |> resolve)
                |> Seq.toArray
        else Array.empty

    /// Substitutes the given bindings in the given schema.
    let rec substitute bindings (schema : Schema) =
        match schema with

                // bind with placeholder
            | Holds (Predicate (name, 0u), terms) ->
                assert(terms.Length = 0)
                match bindings |> Map.tryFind schema with
                    | Some formula -> formula
                    | None -> failwithf "No binding for metavariable %s" name

                // recurse
            | Not formula ->
                Not (
                    formula |> substitute bindings)
            | And (formula1, formula2) ->
                And (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Or (formula1, formula2) ->
                Or (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Implication (formula1, formula2) ->
                Implication (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Biconditional (formula1, formula2) ->
                Biconditional (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)

                // error
            | _ -> failwith "Unexpected"

/// Ordinary rule of inference (i.e. not structured).
type InferenceRule =
    {
        Premises : Schema[]
        Conclusions : Schema[]
    }

module InferenceRule =

    /// Metavariables.
    let private p = MetaVariable.create "P"
    let private q = MetaVariable.create "Q"
    let private r = MetaVariable.create "R"

    /// P
    /// Q
    /// -----
    /// P & Q
    let andIntroduction =
        {
            Premises = [| p; q |]
            Conclusions = [| And (p, q) |]
        }

    /// P & Q
    /// -----
    /// P
    let andEliminationLeft =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| p |]
        }

    /// P & Q
    /// -----
    /// Q
    let andEliminationRight =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| q |]
        }

    /// P
    /// -----
    /// P | Q
    let orIntroductionLeft =
        {
            Premises = [| p |]
            Conclusions = [| Or (p, q) |]
        }

    /// Q
    /// -----
    /// P | Q
    let orIntroductionRight =
        {
            Premises = [| q |]
            Conclusions = [| Or (p, q) |]
        }

    /// P | Q
    /// P -> R
    /// Q -> R
    /// -----
    /// R
    let orElimination =
        {
            Premises =
                [|
                    Or (p, q)
                    Implication (p, r)
                    Implication (q, r)
                |]
            Conclusions = [| r |]
        }

    /// P -> Q
    /// P -> ~Q
    /// -----
    /// ~P
    let notIntroduction =
        {
            Premises =
                [|
                    Implication (p, q)
                    Implication (p, Not q)
                |]
            Conclusions = [| Not p |]
        }

    /// ~~P
    /// -----
    /// P
    let notElimination =
        {
            Premises = [| Not (Not p) |]
            Conclusions = [| p |]
        }

    /// Implication introduction is a structured rule:
    ///
    /// P |- Q  (i.e. Q can be proved from P)
    /// ------
    /// P -> Q
    ///
    /// Implementation is programmatic instead of declarative.

    /// P -> Q
    /// P
    /// ------
    /// Q
    ///
    /// AKA modus ponens.
    let implicationElimination =
        {
            Premises = [| Implication (p, q); p |]
            Conclusions = [| q |]
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalIntroduction =
        {
            Premises =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
            Conclusions = [| Biconditional (p, q) |]
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalElimination =
        {
            Premises = [| Biconditional (p, q) |]
            Conclusions =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
        }

    let allRules =
        [|
            andIntroduction
            andEliminationLeft
            andEliminationRight

            orIntroductionLeft
            orIntroductionRight
            orElimination

            notIntroduction
            notElimination

            implicationElimination

            biconditionalIntroduction
            biconditionalElimination
        |]

    /// Finds all possible applications of the given rule to the
    /// given formulas.
    let apply formulas rule =
        Schema.bind formulas rule.Premises
            |> Array.map (fun binding ->
                rule.Conclusions
                    |> Array.map (Schema.substitute binding))
