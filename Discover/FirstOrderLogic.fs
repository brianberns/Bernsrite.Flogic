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
        let rec loop isRoot = function
            | Holds (Predicate (name, arity), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)
            | Equality (terml, termr) ->
                sprintf "%s = %s" (terml.ToString()) (termr.ToString())
            | Not formula ->
                sprintf "~%s" (formula.ToString())
            | And (formula1, formula2) ->
                sprintf "%s & %s"
                    (formula1 |> loop false)
                    (formula2 |> loop false)
            | Or (formula1, formula2) ->
                sprintf "%s | %s"
                    (formula1 |> loop false)
                    (formula2 |> loop false)
            | Implication (formula1, formula2) ->
                sprintf "%s%s -> %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")
            | Biconditional (formula1, formula2) ->
                sprintf "%s%s <-> %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")
            | Exists (variable, formula) ->
                sprintf "∃%s %s"
                    (variable.ToString())
                    (formula |> loop false)
            | ForAll (variable, formula) ->
                sprintf "∀%s %s"
                    (variable.ToString())
                    (formula |> loop false)
        this |> loop true

    override this.ToString() =
        this.String

// http://www.math.ubc.ca/~cytryn/teaching/scienceOneF10W11/handouts/OS.proof.3inference.html

type InferenceRule =
    Formula (*antecedent template*) * Formula (*consequent template*)

module InferenceRule =

    let formula name =
        Holds (Predicate (name, 0u), [])

    /// (P -> Q) & P => Q
    let modusPonens : InferenceRule =
        let p = formula "P"
        let q = formula "Q"
        And (Implication (p, q), p), q

    /// (P -> Q) & ~Q => ~P
    let modusTollens : InferenceRule =
        let p = formula "P"
        let q = formula "Q"
        And (Implication (p, q), (Not q)), Not p

    let unify template formula =
        let rec loop template formula =
            seq {
                match (template, formula) with
                    | Holds (Predicate (name, 0u), terms), _ ->
                        assert(terms.Length = 0)
                        yield! [Ok (name, formula)]
                    | And (template1, template2), And (formula1, formula2) ->
                        yield! loop template1 formula1
                        yield! loop template2 formula2
                    | Implication (template1, template2), Implication (formula1, formula2) ->
                        yield! loop template1 formula1
                        yield! loop template2 formula2
                    | _ -> yield! [Error "No match"]
            }
        let results =
            loop template formula
                |> Seq.toArray
        let msgOpt =
            results
                |> Array.tryPick (function
                    | Error msg -> Some msg
                    | Ok _ -> None)
        match msgOpt with
            | Some msg -> Error msg
            | None ->
                results
                    |> Seq.choose (function
                        | Error _ -> None
                        | Ok pair -> Some pair)
                    |> Map.ofSeq
                    |> Ok

    let rec substitute (consequent : Formula) (substitutions : Map<Name, Formula>) =
        match consequent with
            | Holds (Predicate (name, 0u), terms) ->
                assert(terms.Length = 0)
                substitutions.[name]
            | And (formula1, formula2) ->
                And (
                    substitute formula1 substitutions,
                    substitute formula2 substitutions)
            | Implication (formula1, formula2) ->
                Implication (
                    substitute formula1 substitutions,
                    substitute formula2 substitutions)
            | _ -> failwith "Unexpected"
