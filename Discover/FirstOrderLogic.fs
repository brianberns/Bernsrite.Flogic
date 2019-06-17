namespace Discover

// http://www.cs.jhu.edu/~phi/ai/slides/lecture-first-order-logic.pdf

type Arity = uint32
type Name = string

type Function = Function of Name * Arity     // produces an "object"
type Predicate = Predicate of Name * Arity   // produces a Boolean
type Variable = Variable of Name

type Term =
    | Variable of Name
    | Constant of Name
    | Application of Function * List<Term>

type Formula =

        // atomic (no sub-formulas)
    | IsTrue of Predicate * List<Term>
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

// http://www.math.ubc.ca/~cytryn/teaching/scienceOneF10W11/handouts/OS.proof.3inference.html

type InferenceRule =
    Formula (*input template*) * Formula (*output template*)

module InferenceRule =

    /// (P -> Q) & P => Q
    let modusPonens : InferenceRule =
        let formula name =
            IsTrue (Predicate (name, 0u), [])
        let P = formula "P"
        let Q = formula "Q"
        And (Implication (P, Q), P), Q

    let unify template formula =
        let rec loop template formula =
            seq {
                match (template, formula) with
                    | (IsTrue (Predicate (_, 0u), terms), _) ->
                        assert(terms.Length = 0)
                        yield template, formula
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
