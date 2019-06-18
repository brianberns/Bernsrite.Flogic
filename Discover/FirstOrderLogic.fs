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
                sprintf "%s%s & %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")
            | Or (formula1, formula2) ->
                sprintf "%s%s | %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")
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

// http://www.mathpath.org/proof/proof.inference.htm

type InferenceRule =
    Formula (*antecedent template*) * Formula (*consequent template*)

module InferenceRule =

    let private formula name =
        Holds (Predicate (name, 0u), [])

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

    let unify template formula =
        let rec loop template formula =
            seq {
                match (template, formula) with
                    | Holds (Predicate (name, 0u), terms), _ ->
                        assert(terms.Length = 0)
                        yield! [Ok (name, formula)]
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
                    | _ -> yield! [
                        sprintf "Can't unify %A with %A" template formula
                            |> Error]
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
                let matches =
                    results
                        |> Array.choose (function
                            | Error _ -> None
                            | Ok pair -> Some pair)
                let groups =
                    matches
                        |> Seq.groupBy fst
                        |> Seq.map (fun (name, group) ->
                            let distinct =
                                group
                                    |> Seq.distinct
                                    |> Seq.toArray
                            name, distinct)
                        |> Seq.toArray
                let conflicts =
                    groups
                        |> Array.choose (fun (name, group) ->
                            if group.Length = 1 then
                                None
                            else
                                let formulas =
                                    group |> Array.map snd
                                Some (name, formulas))
                if conflicts.Length = 0 then
                    matches
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

    let rec substitute (consequent : Formula) (substitutions : Map<Name, Formula>) =
        match consequent with
            | Holds (Predicate (name, 0u), terms) ->
                assert(terms.Length = 0)
                substitutions.[name]
            | Not formula' ->
                Not (
                    substitute formula' substitutions)
            | And (formula1, formula2) ->
                And (
                    substitute formula1 substitutions,
                    substitute formula2 substitutions)
            | Implication (formula1, formula2) ->
                Implication (
                    substitute formula1 substitutions,
                    substitute formula2 substitutions)
            | _ -> failwith "Unexpected"
