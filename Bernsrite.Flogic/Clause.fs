namespace Bernsrite.Flogic

open System

/// A collection of literals that are implicitly ORed together.
[<StructuredFormatDisplay("{String}")>]
type Clause =
    {
        Literals : Literal[]
    }

    /// Display string.
    member this.String =
        this.Literals
            |> Seq.sortBy (fun literal ->
                literal.Predicate)
            |> String.join " | "

    /// Display string.
    override this.ToString() =
        this.String

/// http://intrologic.stanford.edu/public/section.php?section=section_05_02
/// http://www.cs.miami.edu/home/geoff/Courses/COMP6210-10M/Content/FOFToCNF.shtml
/// https://en.wikipedia.org/wiki/Conjunctive_normal_form
module Clause =

    /// The empty clause.
    let empty =
        { Literals = Array.empty }

    /// Creates a clause from the given literals.
    let create literals =
        {
            Literals =
                literals
                    |> Seq.distinct
                    |> Seq.toArray
        }

    /// Applies the given mapping to all literals in the given clause.
    let map mapping clause =
        clause.Literals
            |> Seq.map mapping
            |> create

    /// Converts a formula to clauses.
    let toClauses =

        /// Rewrites biconditionals.
        let rec eliminateBiconditionals formula =
            let (!) = eliminateBiconditionals
            match formula with

                    // P <=> Q to (P => Q) & (Q => P).
                | Biconditional (formula1, formula2) ->
                    let formula1' = !formula1
                    let formula2' = !formula2
                    And (
                        Implication (formula1', formula2'),
                        Implication (formula2', formula1'))

                | _ -> formula |> Formula.transform (!)

        /// Rewrites implications.
        let rec eliminateImplications formula =
            let (!) = eliminateImplications
            match formula with

                    // P => Q to ~P | Q
                | Implication (formula1, formula2) ->
                    Or (Not !formula1, !formula2)

                | _ -> formula |> Formula.transform (!)

        /// Rewrites negations.
        let rec moveNegationsIn formula =
            let (!) = moveNegationsIn
            let (!!) formula = !(Not !formula)
            match formula with

                    // ~(P & Q) to (~P | ~Q)
                | Not (And (formula1, formula2)) ->
                    Or (!!formula1, !!formula2)

                    // ~(P | Q) to (~P & ~Q)
                | Not (Or (formula1, formula2)) ->
                    And (!!formula1, !!formula2)

                    // ~~P to P
                | Not (Not formula) ->
                    !formula

                    // ~∃X.P to ∀X.~P
                | Not (Exists (variable, formula)) ->
                    ForAll (variable, !!formula)

                    // ~∀X.P to ∃X.~P
                | Not (ForAll (variable, formula)) ->
                    Exists (variable, !!formula)

                | _ -> formula |> Formula.transform (!)

        /// Renames variables to avoid conflicts.
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

            let rec loop variableMap seen =

                let binary formula1 formula2 constructor =
                    let formula1', seen' =
                        formula1 |> loop variableMap seen
                    let formula2', seen'' =
                        formula2 |> loop variableMap seen'
                    let result : Formula =
                        constructor (formula1', formula2')
                    result, seen''

                let quantified variable inner constructor =
                    let variable', seen' =
                        variable |> Variable.deconflict seen
                    let variableMap' =
                        variableMap |> Map.add variable variable'
                    let inner', seen'' =
                        inner |> loop variableMap' seen'
                    let result : Formula =
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

        /// Moves quantifiers out.
        let rec moveQuantifiersOut formula =
            let (!) = moveQuantifiersOut
            match formula with

                    // Q & ∀X.P to ∀X.(Q & P)
                | And (formula1, ForAll (variable, formula2)) ->
                    ForAll (variable, !(And (!formula1, !formula2)))

                    // ∀X.P & Q to ∀X.(P & Q)
                | And (ForAll (variable, formula1), formula2) ->
                    ForAll (variable, !(And (!formula2, !formula1)))

                    // Q & ∃X.P to ∃X.(Q & P)
                | And (formula1, Exists (variable, formula2)) ->
                    Exists (variable, !(And (!formula1, !formula2)))

                    // ∃X.P & Q to ∃X.(P & Q)
                | And (Exists (variable, formula2), formula1) ->
                    Exists (variable, !(And (!formula2, !formula1)))

                    // Q | ∀X.P to ∀X.(Q | P)
                | Or (formula1, ForAll (variable, formula2)) ->
                    ForAll (variable, !(Or (!formula1, !formula2)))

                    // ∀X.P | Q to ∀X.(P | Q)
                | Or (ForAll (variable, formula1), formula2) ->
                    ForAll (variable, !(Or (!formula2, !formula1)))

                    // Q | ∃X.P to ∃X.(Q | P)
                | Or (formula1, Exists (variable, formula2)) ->
                    Exists (variable, !(Or (!formula1, !formula2)))

                    // ∃X.P | Q to ∃X.(P | Q)
                | Or (Exists (variable, formula2), formula1) ->
                    Exists (variable, !(Or (!formula2, !formula1)))

                | _ -> formula |> Formula.transform (!)

        /// Removes quantifiers.
        let removeQuantifiers formula =

            let rec loop scope = function

                    // add variable to scope and drop universal quantifier
                | ForAll (variable, inner) ->
                    assert(scope |> Set.contains variable |> not)
                    let scope' = scope |> Set.add variable
                    inner |> loop scope'

                    // skolemize to remove existential quantifier
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

                // add explicit universal quantifier for any free variables
            formula
                |> Formula.getFreeVariables
                |> Seq.fold (fun acc var ->
                    ForAll (var, acc)) formula
                |> loop Set.empty

        /// Distributes disjunctions: moves ANDs outside, ORs inside.
        let rec distributeDisjunctions formula =
            let (!) = distributeDisjunctions
            match formula with

                    // P | (Q & R) to (P | Q) & (P | R)
                | Or (p, And (q, r)) ->
                    let p' = !p
                    And (!(Or (p', !q)), !(Or (p', !r)))

                    // (Q & R) | P to (Q | P) & (R | P)
                | Or (And (q, r), p) ->
                    let p' = !p
                    And (!(Or (!q, p')), !(Or (!r, p')))

                    // fully process ORs (is there a better way?)
                | Or (p, q) ->
                    let formula' = Or (!p, !q)
                    if formula' <> formula then !formula'
                    else formula'

                | _ -> formula |> Formula.transform (!)

        /// Converts a formula in conjunctive normal form to clauses.
        let convertToClauses formulaCnf =

            let rec removeAnds formulas = function
                | And (p, q) ->
                    let formulas' = p |> removeAnds formulas
                    q |> removeAnds formulas'
                | Or _ as formula ->
                    formulas |> Set.add formula
                | Formula _ as formula ->
                    formulas |> Set.add formula
                | Not (Formula _) as formula ->
                    formulas |> Set.add formula
                | _ -> failwith "Not in conjunctive normal form"

            let rec removeOrs literals = function
                | Or (p, q) ->
                    let literals' = p |> removeOrs literals
                    q |> removeOrs literals'
                | Formula _ as formula ->
                    literals
                        |> Set.add (Literal.ofFormula formula)
                | Not (Formula _) as formula ->
                    literals
                        |> Set.add (Literal.ofFormula formula)
                | _ -> failwith "Not in conjunctive normal form"

            formulaCnf
                |> removeAnds Set.empty
                |> Set.map (
                    (removeOrs Set.empty)
                        >> create)

            // main function starts here
        eliminateBiconditionals
            >> eliminateImplications
            >> moveNegationsIn
            >> standardizeVariables
            >> moveQuantifiersOut
            >> removeQuantifiers
            >> distributeDisjunctions
            >> convertToClauses

    /// Applies the given substitution to the given literal.
    let private apply subst literal =
        literal
            |> Literal.map (Substitution.applyTerm subst)

    /// Derives new clauses from the given clauses using the resolution
    /// principle.
    let resolve clause1 clause2 =

        /// Deconflicts variable names in the given clauses by renaming
        /// variables in the second clause as needed.
        let deconflict clauseToKeep clauseToRename =

                // find all variables used in the first clause
            let seen =
                seq {
                    for literal in clauseToKeep.Literals do
                        for term in literal.Terms do
                            yield! term |> Term.getVariables
                } |> set

            let deconflictVariable variable =
                variable
                    |> Variable.deconflict seen
                    |> fst

            let rec deconflictTerm = function
                | Term variable ->
                    variable
                        |> deconflictVariable
                        |> Term
                | Application (func, terms) ->
                    Application (
                        func,
                        terms |> Array.map deconflictTerm)

                // rename variables used in the second clause as needed
            clauseToRename
                |> map (Literal.map deconflictTerm)

        /// Answers all factors of the given clause (including itself).
        let allFactors clause =

            let rec loop clause =
                seq {
                    yield clause
                    for i = 0 to clause.Literals.Length - 1 do
                        for j = 0 to clause.Literals.Length - 1 do
                            if i <> j then
                                match Literal.tryUnify
                                    clause.Literals.[i]
                                    clause.Literals.[j] with
                                    | Some subst ->
                                        yield! clause
                                            |> map (apply subst)
                                            |> loop
                                    | None -> ()
                }

            clause
                |> loop
                |> Seq.toArray

            // isolates each item in the given array
        let createAllButArray mapping (items : _[]) =
            items
                |> Array.mapi (fun i item ->
                    let item' = mapping item
                    let allBut =
                        lazy [|
                            for j = 0 to items.Length - 1 do
                                if i <> j then
                                    yield items.[j]
                        |]
                    item', allBut)

            // deconflict the clauses and find all factors of each one
        let allButArrays1 =
            clause1
                |> allFactors
                |> Seq.map (fun clause ->
                    clause.Literals
                        |> createAllButArray id)
        let allButArrays2 =
            deconflict clause1 clause2
                |> allFactors
                |> Seq.map (fun clause ->
                    clause.Literals
                        |> createAllButArray Literal.negate)   // negate for unification

        seq {
            for allButArray1 in allButArrays1 do
                for allButArray2 in allButArrays2 do
                    for (literal1, allBut1) in allButArray1 do
                        for (literal2, allBut2) in allButArray2 do
                            match Literal.tryUnify literal1 literal2 with
                                | Some subst ->
                                    yield Seq.append allBut1.Value allBut2.Value
                                        |> Seq.map (apply subst)
                                        |> create
                                | None -> ()
        } |> set

    /// Indicates whether the first clause subsumes the second
    /// clause.
    /// http://profs.sci.univr.it/~farinelli/courses/ar/slides/resolution-fol.pdf
    /// https://archive.org/details/symboliclogicmec00chan/page/94
    let subsumes clauseC clauseD =

            // compute substitution θ
        let substTheta =
            let variables =
                clauseD.Literals
                    |> Seq.collect (fun literal ->
                        literal.Terms |> Seq.collect Term.getVariables)
                    |> Seq.distinct
            (Substitution.empty, variables)
                ||> Seq.fold (fun acc variable ->
                    let _, term = Skolem.create Array.empty   // create constant term
                    let sub = Substitution.create variable term
                    Substitution.compose acc sub)

            // compute clauses W from literals of ~Dθ
        let clausesW =
            clauseD.Literals
                |> Array.map (
                    apply substTheta
                        >> Literal.negate
                        >> Seq.singleton
                        >> create)

            // compute set of clauses U(k+1) from U(k)
        let rec loop clausesU =
            if clausesU |> Set.isEmpty then
                false
            elif clausesU |> Set.contains empty then
                true
            else
                seq {
                    for clauseU in clausesU do
                        for clauseW in clausesW do
                            yield! resolve clauseU clauseW
                }
                    |> set
                    |> loop

        set [clauseC] |> loop