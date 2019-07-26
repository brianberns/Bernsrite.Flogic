namespace Bernsrite.Flogic

open System

/// E.g. Mortal(x) is a predicate of arity 1.
[<RequireQualifiedAccess; Struct>]
type Predicate =
    {
        /// Name of this predicate.
        Name : string

        /// Number of arguments.
        Arity : int
    }

module Predicate =

    /// Creates a predicate with the given name and arity.
    let create name arity =
        {
            Predicate.Name = name
            Predicate.Arity = arity
        }

/// E.g. Man(Socrates) -> Mortal(Socrates).
[<StructuredFormatDisplay("{String}")>]
type Formula =

    /// Atomic formula (no sub-formulas): P(t1, t2, ...)
    | Atom of Predicate * Term[]

    /// Negation: ~P
    | Not of Formula

    /// Conjunction: P & Q
    | And of Formula * Formula

    /// Disjunction: P | Q
    | Or of Formula * Formula

    /// Implication: P -> Q
    | Implication of Formula * Formula

    /// Biconditional: P <-> Q
    | Biconditional of Formula * Formula

    /// Existential quantifier: ∃x.P(x)
    | Exists of Variable * Formula

    /// Universal quantifier: ∀x.P(x)
    | ForAll of Variable * Formula

    /// Display string.
    member this.String =

        let rec loop isRoot =

            let infix symbol formula1 formula2 =
                sprintf "%s%s %s %s%s"
                    (if isRoot then "" else "(")
                    (formula1 |> loop false)
                    symbol
                    (formula2 |> loop false)
                    (if isRoot then "" else ")")

            function
                | Atom (predicate, terms) ->
                    Print.application predicate.Name terms true
                | Not (Atom (predicate, terms)) ->
                    Print.application predicate.Name terms false
                | Not formula ->
                    sprintf "~%s" (formula |> loop false)
                | And (formula1, formula2) ->
                    infix "&" formula1 formula2
                | Or (formula1, formula2) ->
                    infix "|" formula1 formula2
                | Implication (formula1, formula2) ->
                    infix "⇒" formula1 formula2
                | Biconditional (formula1, formula2) ->
                    infix "⇔" formula1 formula2
                | Exists (variable, formula) ->
                    sprintf "∃%s.%s"
                        variable.Name
                        (formula |> loop false)
                | ForAll (variable, formula) ->
                    sprintf "∀%s.%s"
                        variable.Name
                        (formula |> loop false)

        this |> loop true

    /// Display string.
    override this.ToString() =
        this.String

module Formula =

    /// Display string.
    let toString (formula : Formula) =
        formula.ToString()

    /// Tries to substitute the given term for the given variable in the given
    /// formula. Fails if this would capture any of the variables in the given
    /// term.
    /// https://math.stackexchange.com/questions/3272333/restrictions-on-existential-introduction-in-first-order-logic
    let trySubstitute variable term formula =

            // variables that must avoid capture
        let termVariables =
            term |> Term.getVariables

        let rec loop formula =

                // substitutes within a unary formula
            let unary formula constructor =
                opt {
                    let! formula' = loop formula
                    return constructor formula'
                }

                // substitutes within a binary formula
            let binary formula1 formula2 constructor =
                opt {
                    let! formula1' = loop formula1
                    let! formula2' = loop formula2
                    return constructor (formula1', formula2')
                }

                // substitutes within a quantified formula
            let quantified oldVariable formula constructor =
                if termVariables.Contains(oldVariable) then
                    None
                else opt {
                    if variable = oldVariable then
                        return constructor (oldVariable, formula)
                    else
                        return! unary formula (fun formula' ->
                            constructor (oldVariable, formula'))
                }

                // substitutes within a formula
            match formula with
                | Atom (predicate, oldTerms) ->
                    Atom (
                        predicate,
                        oldTerms
                            |> Term.substituteTerms variable term)
                        |> Some
                | Not formula ->
                    Not |> unary formula
                | And (formula1, formula2) ->
                    And |> binary formula1 formula2
                | Or (formula1, formula2) ->
                    Or |> binary formula1 formula2
                | Implication (formula1, formula2) ->
                    Implication |> binary formula1 formula2
                | Biconditional (formula1, formula2) ->
                    Biconditional |> binary formula1 formula2
                | Exists (oldVariable, formula) ->
                    Exists |> quantified oldVariable formula
                | ForAll (oldVariable, formula) ->
                    ForAll |> quantified oldVariable formula

        loop formula

    /// Answers the free variables in the given formula.
    let private getFreeVariables formula =

        let rec loop formula =
            seq {
                match formula with
                    | Atom (_, terms) ->
                        for term in terms do
                            yield! term |> Term.getVariables
                    | Not formula ->
                        yield! formula |> loop
                    | And (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Or (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Implication (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Biconditional (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
                    | Exists (variable, formula) ->
                        for var in formula |> loop do
                            if var <> variable then
                                yield var
                    | ForAll (variable, formula) ->
                        for var in formula |> loop do
                            if var <> variable then
                                yield var
            }

        formula
            |> loop
            |> set

    /// Adds an explicit universal quantifier for each free variable.
    let quantifyUniversally formula =
        let result =
            formula
                |> getFreeVariables
                |> Seq.fold (fun acc var ->
                    ForAll (var, acc)) formula
        assert(result |> getFreeVariables |> Set.isEmpty)
        result

    /// Converts the given collection of items to a bag (i.e. multi-set).
    let private toBag items =
        items
            |> Seq.groupBy id
            |> Seq.map (fun (func, group) ->
                let count = group |> Seq.length
                func, count)
            |> Map.ofSeq

    /// Finds all functions contained in the given formula.
    let getFunctions formula =

        let rec loopTerm term =
            seq {
                match term with
                    | Application (func, terms) ->
                        yield func
                        yield! terms |> loopTerms
                    | _ -> ()
            }

        and loopTerms terms =
            terms |> Seq.collect loopTerm

        let rec loopFormula formula =
            seq {
                match formula with
                    | Atom (_, terms) ->
                        yield! terms |> loopTerms
                    | Not formula
                    | Exists (_, formula)
                    | ForAll (_, formula) ->
                        yield! formula |> loopFormula
                    | And (formula1, formula2)
                    | Or (formula1, formula2)
                    | Implication (formula1, formula2)
                    | Biconditional (formula1, formula2) ->
                        yield! formula1 |> loopFormula
                        yield! formula2 |> loopFormula
            }

        formula
            |> loopFormula
            |> toBag

    /// Finds all predicates contained in the given formula.
    let getPredicates formula =

        let rec loop formula =
            seq {
                match formula with
                    | Atom (predicate, _) ->
                        yield predicate
                    | Not formula
                    | Exists (_, formula)
                    | ForAll (_, formula) ->
                        yield! formula |> loop
                    | And (formula1, formula2)
                    | Or (formula1, formula2)
                    | Implication (formula1, formula2)
                    | Biconditional (formula1, formula2) ->
                        yield! formula1 |> loop
                        yield! formula2 |> loop
            }

        formula
            |> loop
            |> toBag

    /// Maps over immediate children. (Easier to understand and work with
    /// than catamorphism.)
    /// http://t0yv0.blogspot.com/2011/09/transforming-large-unions-in-f.html
    let transform func =
        let (!) = func
        function
            | Atom _ as formula -> formula
            | Not formula -> Not (!formula)
            | And (formula1, formula2) -> And (!formula1, !formula2)
            | Or (formula1, formula2) -> Or (!formula1, !formula2)
            | Implication (formula1, formula2) -> Implication (!formula1, !formula2)
            | Biconditional (formula1, formula2) -> Biconditional (!formula1, !formula2)
            | Exists (variable, formula) -> Exists (variable, !formula)
            | ForAll (variable, formula) -> ForAll (variable, !formula)
