namespace Discover

open System

/// Make union case private to this module.
/// https://github.com/dotnet/fsharp/issues/984
[<AutoOpen>]
module LiteralAutoOpen =

    /// A literal is either an atomic formula or its negation.
    [<StructuredFormatDisplay("{String}")>]
    type Literal =
        private | Literal of Formula

        /// Display string.
        member this.String =
            match this with
                | Literal formula -> formula.String

        /// Display string.
        override this.ToString() =
            this.String

    /// Active pattern to deconstruct a literal.
    let (|LiteralAtom|LiteralNot|) = function
        | Literal (Formula (predicate, terms)) ->
            LiteralAtom (predicate, terms)
        | Literal (Not (Formula (predicate, terms))) ->
            LiteralNot (predicate, terms)
        | _ -> failwith "Unexpected"

    module Literal =

        /// Converts a formula to a literal.
        let ofFormula = function
            | Formula _ as formula -> Literal formula
            | Not (Formula _) as formula -> Literal formula
            | _ -> failwith "Not a literal"

module Literal =

    /// Display string.
    let toString (literal : Literal) =
        literal.ToString()

/// A set of literals that are implicitly ORed together.
[<StructuredFormatDisplay("{String}")>]
type Clause =
    | Clause of Set<Literal>

    /// Display string.
    member this.String =
        match this with
            | Clause literals ->
                let strs =
                    literals
                        |> Seq.map Literal.toString
                String.Join(" | ", strs)

    /// Display string.
    override this.ToString() =
        this.String

/// http://intrologic.stanford.edu/public/section.php?section=section_05_02
/// http://www.cs.miami.edu/home/geoff/Courses/COMP6210-10M/Content/FOFToCNF.shtml
/// https://en.wikipedia.org/wiki/Conjunctive_normal_form
module Clause =

    /// Rewrites biconditionals.
    let rec private eliminateBiconditionals formula =
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
    let rec private eliminateImplications formula =
        let (!) = eliminateImplications
        match formula with

                // P => Q to ~P | Q
            | Implication (formula1, formula2) ->
                Or (Not !formula1, !formula2)

            | _ -> formula |> Formula.transform (!)

    /// Rewrites negations.
    let rec private moveNegationsIn formula =
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
    let private standardizeVariables formula =

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
    let rec private moveQuantifiersOut formula =
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
    let private removeQuantifiers formula =

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
    let rec private distributeDisjunctions formula =
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
    let private convertToClauses formulaCnf =

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
            |> Set.map (removeOrs Set.empty >> Clause)

    /// Converts a formula to clauses.
    let toClauses =
        eliminateBiconditionals
            >> eliminateImplications
            >> moveNegationsIn
            >> standardizeVariables
            >> moveQuantifiersOut
            >> removeQuantifiers
            >> distributeDisjunctions
            >> convertToClauses

    /// The empty clause.
    let empty =
        Clause Set.empty

    /// Applies the given mapping to all literals in the
    /// given clause.
    let map mapping (Clause literals) =
        literals
            |> Set.map mapping
            |> Clause
