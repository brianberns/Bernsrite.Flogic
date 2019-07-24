namespace Bernsrite.Flogic

open System

/// A collection of literals that are implicitly ORed together.
[<CustomEquality; CustomComparison; StructuredFormatDisplay("{String}")>]
type Clause =
    private {

        /// Literals in this set.
        Literals : Set<Literal>

        /// Number of symbols in this clause. (Cached for
        /// performance.)
        SymbolCount : int

        /// Variables contained in this clause. (Cached for
        /// performance).
        Variables : Lazy<Set<Variable>>
    }

    /// Strongly-typed equality.
    member this.Equals(clause) =
        clause.SymbolCount = this.SymbolCount
            && clause.Literals = this.Literals

    /// Weakly-typed equality.
    /// Sadly, F# uses this: https://zeckul.wordpress.com/2015/07/09/how-to-avoid-boxing-value-types-in-f-equality-comparisons/
    override this.Equals(obj) =
        this.Equals(obj :?> Clause)

    interface IEquatable<Clause> with

        /// Strongly-typed equality.
        member this.Equals(clause) =
            this.Equals(clause)

    /// Hash code.
    override this.GetHashCode() =
        this.Literals.GetHashCode()

    /// Strongly-type comparison.
    member this.CompareTo(clause) =
        match compare this.SymbolCount clause.SymbolCount with
            | 0 -> compare this.Literals clause.Literals
            | result -> result

    interface IComparable with

        /// Weakly-typed comparison.
        member this.CompareTo(obj) =
            this.CompareTo(obj :?> Clause)

    interface IComparable<Clause> with

        /// Strongly-type comparison.
        member this.CompareTo(clause) =
            this.CompareTo(clause)

    /// Indicates whether the receiver is empty.
    member this.IsEmpty =
        this.Literals.Count = 0

    /// Display string.
    member this.String =
        if this.IsEmpty then "Contradiction"   // empty clause indicates contradiction
        else
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
        {
            Literals = Set.empty
            SymbolCount = 0
            Variables = lazy Set.empty
        }

    /// Creates a clause.
    let private createRaw literals symbolCount =
        assert(
            symbolCount =
                (literals |> Seq.sumBy Literal.symbolCount))
        {
            Literals = literals
            SymbolCount = symbolCount
            Variables =
                lazy (seq {
                    for literal in literals do
                        for term in literal.Terms do
                            yield! term |> Term.getVariables
                } |> set)
        }

    /// Creates a clause from the given literals.
    let create literals =
        let literalSet = set literals
        let symbolCount =
            literalSet |> Seq.sumBy Literal.symbolCount
        createRaw literalSet symbolCount

    /// Applies the given mapping to all literals in the given clause.
    let map mapping clause =
        clause.Literals
            |> Seq.map mapping
            |> create

    /// Number of symbols in the given clause.
    let symbolCount clause =
        clause.SymbolCount

    /// Converts a clause to literals.
    let toLiterals clause =
        clause.Literals |> Seq.toArray

    /// Converts a clause to a formula.
    let toFormula clause =
        clause.Literals
            |> Seq.map Literal.toFormula
            |> Seq.reduce (fun formula1 formula2 ->
                Or (formula1, formula2))

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
                | VariableTerm variable ->
                    variable
                        |> standardizeVariable variableMap
                        |> VariableTerm 
                | ConstantTerm _ as term -> term
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
                    | Atom (predicate, terms) ->
                        let result =
                            Atom (
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
                    let skolem =
                        scope
                            |> Seq.map VariableTerm
                            |> Seq.toArray
                            |> Skolem.create
                    inner
                        |> Formula.trySubstitute variable skolem
                        |> Option.defaultWith (fun () ->
                            failwith "Substitution failed")
                        |> loop scope

                | _ as formula ->
                    formula |> Formula.transform (loop scope)

            formula
                |> Formula.quantifyUniversally
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

                    // maintain order of formulas
                | And (p, q) ->
                    let formulas' = q |> removeAnds formulas
                    p |> removeAnds formulas'
                | Or _ as formula ->
                    formula :: formulas
                | Atom _ as formula ->
                    formula :: formulas
                | Not (Atom _) as formula ->
                    formula :: formulas
                | _ -> failwith "Not in conjunctive normal form"

            let rec removeOrs literals = function
                | Or (p, q) ->
                    let literals' = p |> removeOrs literals
                    q |> removeOrs literals'
                | Atom _ as formula ->
                    literals
                        |> Set.add (Literal.ofFormula formula)
                | Not (Atom _) as formula ->
                    literals
                        |> Set.add (Literal.ofFormula formula)
                | _ -> failwith "Not in conjunctive normal form"

            formulaCnf
                |> removeAnds List.empty
                |> Seq.map (
                    (removeOrs Set.empty)
                        >> create)
                |> Seq.toArray

            // main function starts here
        eliminateBiconditionals
            >> eliminateImplications
            >> moveNegationsIn
            >> standardizeVariables
            >> moveQuantifiersOut
            >> removeQuantifiers
            >> distributeDisjunctions
            >> convertToClauses

    /// Permutes the literals in the given clause.
    let private permute clause =
        let literals =
            clause.Literals |> Seq.toArray
        seq {
            for i = 0 to literals.Length - 1 do
                for j = i + 1 to literals.Length - 1 do
                    yield literals.[i], literals.[j]
        }

    /// Indicates whether the given clause is a tautology (i.e. always
    /// true).
    let isTautology clause =
        clause
            |> permute
            |> Seq.exists (fun (literal1, literal2) ->
                literal1.Predicate = literal2.Predicate
                    && literal1.IsPositive <> literal2.IsPositive
                    && literal1.Terms = literal2.Terms)

    /// Applies the given substitution to the given literal.
    let private apply subst literal =
        literal
            |> Literal.map (Substitution.applyTerm subst)

    /// Derives new clauses from the given clauses using the resolution principle.
    /// https://www.doc.ic.ac.uk/~kb/MACTHINGS/SLIDES/2013Notes/6LSub4up13.pdf
    let resolve clause1 clause2 =

        /// Deconflicts variable names in the given clauses by renaming
        /// variables in the second clause as needed.
        let deconflict clauseToKeep clauseToRename =

                // find conflicting variables
            let intersection =
                Set.intersect
                    clauseToKeep.Variables.Value
                    clauseToRename.Variables.Value
            if intersection.IsEmpty then clauseToRename
            else
                    // find variables already in use
                let union =
                    Set.union
                        clauseToKeep.Variables.Value
                        clauseToRename.Variables.Value

                    // resolve each conflict one at a time
                let literals, _, _ =
                    ((clauseToRename.Literals, union, Map.empty), intersection)
                        ||> Seq.fold (fun (literals, variables, variableMap) variable ->
                            let variable', variables' =
                                variable |> Variable.deconflict variables
                            let variableMap' =
                                variableMap |> Map.add variable variable'
                            let literals' =
                                literals
                                    |> Set.map (Literal.substitute variable (VariableTerm variable'))
                            literals', variables', variableMap')
                createRaw literals clauseToRename.SymbolCount

            // isolates each item in the given array
        let createAllButArray mapping items =
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

            // deconflict the clauses and prepare to unify their literals
        let allButArray1 =
            clause1
                |> toLiterals
                |> createAllButArray id
        let allButArray2 =
            deconflict clause1 clause2
                |> toLiterals
                |> createAllButArray Literal.negate   // negate for unification

        seq {
            for literal1, allBut1 in allButArray1 do
                for literal2, allBut2 in allButArray2 do
                    match Literal.tryUnify literal1 literal2 with
                        | Some subst ->
                            let resolvent =
                                Seq.append allBut1.Value allBut2.Value
                                    |> Seq.map (apply subst)
                                    |> create   // eliminate duplicate literals
                            yield resolvent, subst
                        | None -> ()
        }
            |> Seq.distinctBy fst
            |> Seq.toArray

    /// Answers all factors of the given clause (including itself).
    let allFactors clause =

        let rec loop clause =
            seq {
                yield clause
                for literal1, literal2 in permute clause do
                    match Literal.tryUnify literal1 literal2 with
                        | Some subst ->
                            yield! clause
                                |> map (apply subst)
                                |> loop
                        | None -> ()
            }

        clause
            |> loop
            |> Seq.toArray

    /// Indicates whether the first clause subsumes the second clause.
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
                    let term = Skolem.create Array.empty   // create constant term
                    let sub = Substitution.create variable term
                    Substitution.compose acc sub)

            // compute clauses W from literals of ~Dθ
        let clausesW =
            clauseD.Literals
                |> Seq.map (
                    apply substTheta
                        >> Literal.negate
                        >> Seq.singleton
                        >> create)
                |> Seq.toArray

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
                                |> Seq.map fst
                }
                    |> set
                    |> loop

        set [clauseC] |> loop