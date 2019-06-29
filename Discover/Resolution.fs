namespace Discover

type Clause = Set<Formula>

/// http://intrologic.stanford.edu/public/section.php?section=section_05_02
module Resolution =

    let rec private eliminateBiconditionals formula =
        let (!) = eliminateBiconditionals
        match formula with
            | Biconditional (formula1, formula2) ->
                let formula1' = !formula1
                let formula2' = !formula2
                And (
                    Implication (formula1', formula2'),
                    Implication (formula2', formula1'))
            | _ -> formula |> Formula.transform (!)

    let rec private eliminateImplications formula =
        let (!) = eliminateImplications
        match formula with
            | Implication (formula1, formula2) ->
                Or (Not !formula1, !formula2)
            | Biconditional _ -> failwith "Unexpected"
            | _ -> formula |> Formula.transform (!)

    let rec private moveNegationsIn formula =
        let (!) = moveNegationsIn
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
            | _ -> formula |> Formula.transform (!)

    /// https://en.wikipedia.org/wiki/Negation_normal_form
    let toNegationNormalForm formula =
        formula
            |> eliminateBiconditionals
            |> eliminateImplications
            |> moveNegationsIn

    /// https://en.wikipedia.org/wiki/Conjunctive_normal_form
    let standardizeVariables formula =

        let standardizeVariable variableMap variable =
            variableMap
                |> Map.tryFind variable
                |> Option.defaultValue variable

        let rec standardizeTerm variableMap = function
            | Term variable ->
                variable
                    |> standardizeVariable variableMap
                    |> Term 
            | Application (func, terms) ->
                Application (
                    func,
                    terms |> standardizeTerms variableMap)

        and standardizeTerms variableMap terms =
            terms |> Array.map (standardizeTerm variableMap)

        let rec obtainVariable seen ((Variable name) as variable) =
            if seen |> Set.contains(variable) then
                Variable (name + "'") |> obtainVariable seen
            else
                let seen' = seen |> Set.add variable
                variable, seen'

        let rec loop variableMap seen =

            let binary formula1 formula2 constructor =
                let formula1', seen' =
                    formula1 |> loop variableMap seen
                let formula2', seen'' =
                    formula2 |> loop variableMap seen'
                let result =
                    constructor (formula1', formula2')
                result, seen''

            let quantified variable inner constructor =
                let variable', seen' =
                    variable |> obtainVariable seen
                let variableMap' =
                    assert(variableMap |> Map.containsKey variable |> not)
                    variableMap |> Map.add variable variable'
                let inner', seen'' =
                    inner |> loop variableMap' seen'
                let result =
                    constructor (variable', inner')
                result, seen''

            function
                | Formula (predicate, terms) ->
                    let result =
                        Formula (
                            predicate,
                            terms |> standardizeTerms variableMap)
                    result, seen
                | Not formula ->
                    let formula', seen' =
                        formula |> loop variableMap seen
                    (Not formula'), seen'
                | And (formula1, formula2) ->
                    And |> binary formula1 formula2
                | Or (formula1, formula2) ->
                    Or |> binary formula1 formula2
                | Implication (formula1, formula2) ->
                    Implication |> binary formula1 formula2
                | Biconditional (formula1, formula2) ->
                    Biconditional |> binary formula1 formula2
                | Exists (variable, inner) ->
                    Exists |> quantified variable inner
                | ForAll (variable, inner) ->
                    ForAll |> quantified variable inner

        let formula', _ =
            formula |> loop Map.empty Set.empty
        formula'

    let rec moveQuantifiersOut formula =
        let (!) = moveQuantifiersOut
        match formula with
            | And (formula1, ForAll (variable, formula2)) ->
                ForAll (variable, !(And (!formula1, !formula2)))
            | And (ForAll (variable, formula1), formula2) ->
                ForAll (variable, !(And (!formula2, !formula1)))
            | And (formula1, Exists (variable, formula2)) ->
                Exists (variable, !(And (!formula1, !formula2)))
            | And (Exists (variable, formula2), formula1) ->
                Exists (variable, !(And (!formula2, !formula1)))
            | Or (formula1, ForAll (variable, formula2)) ->
                ForAll (variable, !(Or (!formula1, !formula2)))
            | Or (ForAll (variable, formula1), formula2) ->
                ForAll (variable, !(Or (!formula2, !formula1)))
            | Or (formula1, Exists (variable, formula2)) ->
                Exists (variable, !(Or (!formula1, !formula2)))
            | Or (Exists (variable, formula2), formula1) ->
                Exists (variable, !(Or (!formula2, !formula1)))
            | _ -> formula |> Formula.transform (!)

    let skolemize formula =

        let rec loop scope = function
            | ForAll (variable, inner) ->
                assert(scope |> Set.contains variable |> not)
                let scope' = scope |> Set.add variable
                inner |> loop scope'
            | Exists (variable, inner) ->
                let _, skolem =
                    scope
                        |> Seq.map Term
                        |> Seq.toArray
                        |> Skolem.create
                inner
                    |> Formula.trySubstitute variable skolem
                    |> Option.defaultWith (fun () ->
                        failwith "Substitution failed")
                    |> loop scope
            | _ as formula ->
                formula |> Formula.transform (loop scope)

        let formula' =
            formula
                |> Formula.getFreeVariables
                |> Seq.fold (fun acc var ->
                    ForAll (var, acc)) formula
        assert(formula' |> Formula.getFreeVariables |> Set.isEmpty)
        formula' |> loop Set.empty
