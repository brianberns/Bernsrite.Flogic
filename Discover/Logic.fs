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

module Result =

    let tryGet = function
        | Ok value -> Some value
        | Error _ -> None

    let isError = function
        | Ok _ -> false
        | Error _ -> true

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

module Schema =

    /// Finds possible bindings of the given formula to the given
    /// schema (including potentially incompatible ones).
    let private bindRaw formula schema =

        let rec loop formula (schema : Schema) =
            seq {
                match (formula, schema) with

                        // bind metavariable
                    | _, Holds (Predicate (_, 0u), terms) ->
                        assert(terms.Length = 0)
                        yield Ok ((schema : MetaVariable), formula)

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

                        // error
                    | _ -> yield sprintf "Can't bind %A to %A" schema formula
                            |> Error
            }

        schema
            |> loop formula
            |> Seq.toArray

    let private resolve rawResults =

            // did an error occur?
        let msgOpt =
            rawResults
                |> Array.tryPick (function
                    | Error msg -> Some msg
                    | Ok _ -> None)

            // create result
        match msgOpt with
            | Some msg -> Error msg
            | None ->

                    // gather bindings
                let bindings : (MetaVariable * Formula)[] =
                    rawResults
                        |> Array.choose (function
                            | Error _ -> None
                            | Ok pair -> Some pair)

                    // look for binding conflicts
                let conflicts =
                    bindings
                        |> Seq.groupBy fst
                        |> Seq.map (fun (metaVar, group) ->
                            let distinct =
                                group
                                    |> Seq.map snd
                                    |> Seq.distinct
                                    |> Seq.toArray
                            metaVar, distinct)
                        |> Seq.choose (fun (metaVar, formulas) ->
                            if formulas.Length = 1 then
                                None
                            else
                                Some (metaVar, formulas))
                        |> Seq.toArray

                    // package into a result
                if conflicts.Length = 0 then
                    bindings
                        |> Map.ofSeq
                        |> Ok
                else
                    let conflicts =
                        conflicts
                            |> Array.map (fun (metaVar, formulas) ->
                                sprintf "(%A conflicts: %s)"
                                    metaVar
                                    (String.Join(", ", formulas)))
                    String.Join(", ", conflicts)
                        |> Error

    let bind formulas schemas =
        if Array.length formulas >= Array.length schemas then
            formulas
                |> List.ofArray
                |> List.permutations schemas.Length
                |> Seq.tryPick (fun formulaList ->
                    Seq.zip formulaList schemas
                        |> Seq.collect (fun (formula, schema) ->
                            schema |> bindRaw formula)
                        |> Seq.toArray
                        |> resolve
                        |> Result.tryGet)
        else None

    /// Substitutes the given bindings in the given schema.
    let rec substitute (bindings : Map<MetaVariable, Formula>) (schema : Schema) =
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

                // error
            | _ -> failwith "Unexpected"

type InferenceRule =
    {
        Premises : Schema[]
        Conclusion : Schema
    }

module InferenceRule =

    /// Placeholders.
    let private p = MetaVariable.create "P"
    let private q = MetaVariable.create "Q"
    let private r = MetaVariable.create "R"
    let private s = MetaVariable.create "S"

    /// AKA modus ponens.
    let implicationElimination =
        {
            Premises = [| Implication (p, q); p |]
            Conclusion = q
        }

    let implicationCreation =
        {
            Premises = [| q |]
            Conclusion = Implication (p, q)
        }

    let implicationDistribution =
        {
            Premises =
                [|
                    Implication (
                        p,
                        Implication (q, r))
                |]
            Conclusion =
                Implication (
                    Implication (p, q),
                    Implication (p, r))
        }

    let allRules =
        [|
            implicationElimination
            // implicationCreation
            // implicationDistribution
        |]

    /// Tries to apply the given rule to the given formulas.
    let tryApply formulas rule =
        Schema.bind formulas rule.Premises
            |> Option.map (fun bindings ->
                rule.Conclusion |> Schema.substitute bindings)

    (*
    let prove premise conclusion rules =
        let rec loop steps formula =
            let childSteps =
                rules
                    |> Seq.choose (fun rule ->
                        rule
                            |> apply formula
                            |> Result.tryGet
                            |> Option.map (fun child ->
                                child, rule))
                    |> Seq.toArray
            let stepOpt =
                childSteps
                    |> Array.tryFind (fun (child, _) ->
                        child = conclusion)
            match stepOpt with
                | Some step ->
                    Some (step :: steps)
                | None ->
                    childSteps
                        |> Array.tryPick (fun (child, _) ->
                            child |> loop steps)
        premise
            |> loop []
            |> Option.map (List.rev >> Array.ofList)
    *)
