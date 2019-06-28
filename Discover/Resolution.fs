﻿namespace Discover

type Clause = Set<Formula>

/// http://intrologic.stanford.edu/public/section.php?section=section_05_02
module Resolution =

    (*
    let isAtomic = function
        | Formula ((Predicate _), _) -> true
        | _ -> false

    let isLiteral = function
        | formula when isAtomic formula -> true
        | Not formula when isAtomic formula -> true
        | _ -> false

    let private validate (clause : Clause) =
        if clause |> Set.forall isLiteral |> not then
            failwith "Invalid clause"

    let create formulas : Clause =
        let clause = set formulas
        validate clause
        clause

    let toClauses formula : Set<Clause> =

        let rec loop = function
            | formula when isLiteral formula ->
                formula

                // Implications
            | Implication (formula1, formula2) ->
                Or (
                    (Not formula1),
                    formula2)
                    |> toClause
            | Biconditional (formula1, formula2) ->
                And (
                    Or (
                        Not formula1,
                        formula2),
                    Or (
                        formula1,
                        Not formula2))
                        |> toClause

                // Negations
            | Not (Not formula) ->
                formula |> toClause
            | Not (And (formula1, formula2)) ->
                Or (
                    Not formula1,
                    Not formula2)
                    |> toClause
            | Not (Or (formula1, formula2)) ->
                And (
                    Not formula1,
                    Not formula2)
                    |> toClause

                // Distribution
            | And (formula1, Or (formula2, formula3)) ->
                And (
                    Or (formula1, formula2),
                    Or (formula1, formula3))
            | Or (And (formula1, formula2), formula3) ->
                And (
                    Or (formula1, formula3),
                    Or (formula2, formula3))
    *)

    let rec private eliminateBiconditionals formula =
        let (!) = eliminateBiconditionals
        match formula with
            | Biconditional (formula1, formula2) ->
                let formula1' = !formula1
                let formula2' = !formula2
                And (
                    Implication (formula1', formula2'),
                    Implication (formula2', formula1'))
            | _ as formula ->
                formula |> Formula.transform (!)

    let rec private eliminateImplications formula =
        let (!) = eliminateImplications
        match formula with
            | Implication (formula1, formula2) ->
                Or (Not !formula1, !formula2)
            | Biconditional _ -> failwith "Unexpected"
            | _ as formula ->
                formula |> Formula.transform (!)

    let rec private pushNegationsIn formula =
        let (!) = pushNegationsIn
        let (!!) formula = !(Not !formula)
        match formula with
            | Not (And (formula1, formula2)) ->
                Or (!!formula1, !!formula2)
            | Not (Or (formula1, formula2)) ->
                And (!!formula1, !!formula2)
            | Not (Not formula) ->
                !formula
            | Not (Exists (variable, formula)) ->
                ForAll (variable, !!formula)
            | Not (ForAll (variable, formula)) ->
                Exists (variable, !!formula)
            | Implication _
            | Biconditional _ -> failwith "Unexpected"
            | _ as formula -> formula |> Formula.transform (!)

    /// https://en.wikipedia.org/wiki/Negation_normal_form
    let toNegationNormalForm formula =
        formula
            |> eliminateBiconditionals
            |> eliminateImplications
            |> pushNegationsIn