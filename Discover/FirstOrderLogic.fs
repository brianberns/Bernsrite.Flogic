namespace Discover

open System

// http://www.cs.jhu.edu/~phi/ai/slides/lecture-first-order-logic.pdf

type Arity = uint32
type Name = string

type Function = Function of Name * Arity     // produces an "object"
type Predicate = Predicate of Name * Arity   // produces a Boolean
type Variable = Variable of Name

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
                    sprintf "∃%A %s"
                        variable
                        (formula |> loop false)
                | ForAll (variable, formula) ->
                    sprintf "∀%A %s"
                        variable
                        (formula |> loop false)

        this |> loop true

    override this.ToString() =
        this.String

module Formula =

    /// Tries to unify the given template to the given fomula.
    let unify template formula =

            // unify recursively
        let rec loop template formula =
            seq {
                match (template, formula) with

                        // unify with placeholder
                    | Holds (Predicate (name, 0u), terms), _ ->
                        assert(terms.Length = 0)
                        yield Ok (name, formula)

                        // recurse
                    | Not template', Not formula' ->
                        yield! loop template' formula'
                    | And (template1, template2), And (formula1, formula2) ->
                        yield! loop template1 formula1
                        yield! loop template2 formula2
                    | Or (template1, template2), Or (formula1, formula2) ->
                        yield! loop template1 formula1
                        yield! loop template2 formula2
                    | Implication (template1, template2), Implication (formula1, formula2) ->
                        yield! loop template1 formula1
                        yield! loop template2 formula2

                        // error
                    | _ -> yield sprintf "Can't unify %A with %A" template formula
                            |> Error
            }

            // get raw results
        let results =
            loop template formula
                |> Seq.toArray

            // did an error occur?
        let msgOpt =
            results
                |> Array.tryPick (function
                    | Error msg -> Some msg
                    | Ok _ -> None)

            // create result
        match msgOpt with
            | Some msg -> Error msg
            | None ->

                    // gather bindings
                let bindings =
                    results
                        |> Array.choose (function
                            | Error _ -> None
                            | Ok pair -> Some pair)

                    // look for binding conflicts
                let conflicts =
                    bindings
                        |> Seq.groupBy fst
                        |> Seq.map (fun (name, group) ->
                            let distinct =
                                group
                                    |> Seq.map snd
                                    |> Seq.distinct
                                    |> Seq.toArray
                            name, distinct)
                        |> Seq.choose (fun (name, formulas) ->
                            if formulas.Length = 1 then
                                None
                            else
                                Some (name, formulas))
                        |> Seq.toArray

                    // package into a result
                if conflicts.Length = 0 then
                    bindings
                        |> Map.ofSeq
                        |> Ok
                else
                    let conflicts =
                        conflicts
                            |> Array.map (fun (name, formulas) ->
                                sprintf "(%s conflicts: %s)"
                                    name
                                    (String.Join(", ", formulas)))
                    String.Join(", ", conflicts)
                        |> Error

    /// Substitutes the given bindings in the given formula.
    let rec substitute bindings = function

            // bind with placeholder
        | Holds (Predicate (name, 0u), terms) ->
            assert(terms.Length = 0)
            match bindings |> Map.tryFind name with
                | Some formula -> formula
                | None -> failwithf "No binding for %s" name

            // recurse
        | Not formula ->
            Not (
                formula |> substitute bindings)
        | And (formula1, formula2) ->
            And (
                formula1 |> substitute bindings,
                formula2 |> substitute bindings)
        | Implication (formula1, formula2) ->
            Implication (
                formula1 |> substitute bindings,
                formula2 |> substitute bindings)

            // error
        | _ -> failwith "Unexpected"

module Result =

    let tryGet = function
        | Ok value -> Some value
        | Error _ -> None

    let isError = function
        | Ok _ -> false
        | Error _ -> true

type InferenceRule =
    Formula (*antecedent template*) * Formula (*consequent template*)

/// http://www.mathpath.org/proof/proof.inference.htm
module InferenceRule =

    /// Creates a 0-arity placeholder for a predicate.
    let private formula name =
        Holds (Predicate (name, 0u), [])

    /// Placeholders.
    let private p = formula "P"
    let private q = formula "Q"
    let private r = formula "R"
       
    /// (P -> Q) & P => Q
    let modusPonens : InferenceRule =
        And (
            Implication (p, q),
            p),
        q

    /// (P -> Q) & ~Q => ~P
    let modusTollens : InferenceRule =
        And (
            Implication (p, q),
            (Not q)),
        Not p

    /// (P -> Q) & (Q -> R) => (P -> Q)
    let hypotheticalSyllogism : InferenceRule =
        And (
            Implication (p, q),
            Implication (q, r)),
        Implication (p, r)

    /// (P | Q) & ~P => Q
    let disjunctiveSyllogism : InferenceRule =
        And (
            Or (p, q),
            Not p),
        q

    let allRules =
        [|
            modusPonens
            modusTollens
            hypotheticalSyllogism
            disjunctiveSyllogism
        |]

    /// Tries to apply the given rule to the given formula.
    let apply formula ((antecedent, consequent) : InferenceRule) =
        formula
            |> Formula.unify antecedent
            |> Result.map (fun bindings ->
                consequent |> Formula.substitute bindings)

    let prove premise conclusion =
        let rec loop steps formula =
            let childSteps =
                allRules
                    |> Array.choose (fun rule ->
                        rule
                            |> apply formula
                            |> Result.tryGet
                            |> Option.map (fun child ->
                                child, rule))
            let stepOpt =
                childSteps
                    |> Array.tryFind (fun (child, _) ->
                        child = conclusion)
            match stepOpt with
                | Some step -> Some (step :: steps)
                | None ->
                    childSteps
                        |> Array.tryPick (fun (child, _) ->
                            child |> loop steps)
        premise
            |> loop []
            |> Option.map (List.rev >> Array.ofList)
