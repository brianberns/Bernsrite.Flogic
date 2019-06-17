namespace Discover

open System

// http://www.cs.jhu.edu/~phi/ai/slides/lecture-first-order-logic.pdf

type Arity = uint32
type Name = string

type Function = Function of Name * Arity     // produces an "object"
type Predicate = Predicate of Name * Arity   // produces a Boolean
type Variable = Variable of Name

type Term =
    | Variable of Name
    | Application of Function * List<Term>

    override this.ToString() =
        match this with
            | Variable name -> name
            | Application ((Function (name, arity)), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)

type Formula =

        // atomic (no sub-formulas)
    | Holds of Predicate * List<Term>
    | Equality of Term * Term

        // negation
    | Negate of Formula

        // binary connectives
    | And of Formula * Formula
    | Or of Formula * Formula
    | Implication of Formula * Formula
    | Biconditional of Formula * Formula

        // quantifiers
    | Exists of Variable * Formula
    | ForAll of Variable * Formula

    override this.ToString() =
        let rec loop isRoot = function
            | Holds (Predicate (name, arity), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)
            | Equality (terml, termr) ->
                sprintf "%s = %s" (terml.ToString()) (termr.ToString())
            | Negate formula ->
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

// http://www.math.ubc.ca/~cytryn/teaching/scienceOneF10W11/handouts/OS.proof.3inference.html

type InferenceRule =
    Formula (*input template*) * Formula (*output template*)

module InferenceRule =

    /// (P -> Q) & P => Q
    let modusPonens : InferenceRule =
        let formula name =
            Holds (Predicate (name, 0u), [])
        let p = formula "P"
        let q = formula "Q"
        And (Implication (p, q), p), q

    let unify template formula =
        let rec loop template formula =
            seq {
                match (template, formula) with
                    | (Holds (Predicate (name, 0u), terms), _) ->
                        assert(terms.Length = 0)
                        yield name, formula
                    | (And (templ1, templ2), And (form1, form2)) ->
                        yield! loop templ1 form1
                        yield! loop templ2 form2
                    | (Implication (templ1, templ2), Implication (form1, form2)) ->
                        yield! loop templ1 form1
                        yield! loop templ2 form2
                    | _ -> ()
            }
        loop template formula
            |> Seq.distinct
            |> Seq.toArray
