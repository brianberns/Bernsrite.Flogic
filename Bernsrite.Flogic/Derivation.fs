namespace Bernsrite.Flogic

/// A resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type Derivation =
    {
        /// Input clauses: premises plus negatated goal.
        InputClauses : Clause[]

        /// Top clause (will be one of the negated goal clauses).
        TopClause : Clause

        /// Clauses derived via linear resolution.
        DerivedClauses : List<Clause>
    }

    /// Display string.
    member this.String =
        seq {

            yield "Input clauses:"
            for clause in this.InputClauses do
                yield sprintf "   %A" clause

            yield sprintf "0. %A" this.TopClause

            let pairs =
                this.DerivedClauses
                    |> List.rev
                    |> Seq.mapi (fun i clause -> i, clause)
            for i, clause in pairs do
                yield sprintf "%d. %A" (i + 1) clause

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

/// Proof via resolution.
module Derivation =

    /// Attempts to prove the given goal from the given premises via
    /// linear resolution.
    /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
    let tryProve premises goal =

            // convert formulas to clauses
        let goalClauses =
            goal
                |> Not   // proof by refutation: negate goal
                |> Clause.toClauses
                |> Seq.toArray
        let inputClauses =
            [|
                yield! premises
                    |> Seq.collect Clause.toClauses
                    |> Seq.toArray
                yield! goalClauses
            |]
            
            // depth-first search
        let search maxDepth derivation =

            let rec loop depth derivation =
                if depth < maxDepth then

                        // get current center clause
                    let centerClause =
                        derivation.DerivedClauses
                            |> List.tryHead
                            |> Option.defaultValue derivation.TopClause

                        // combine with available side clauses
                    Seq.append derivation.InputClauses derivation.DerivedClauses
                        |> Seq.tryPick (fun sideClause ->
                            Clause.resolve centerClause sideClause
                                |> Seq.tryPick (fun resolvent ->
                                    let nextDerivation =
                                        {
                                            derivation with
                                                DerivedClauses =
                                                    resolvent
                                                        :: derivation.DerivedClauses
                                        }
                                    if resolvent.Literals.Length = 0 then   // success: empty clause is a contradiction
                                        Some nextDerivation
                                    else
                                        nextDerivation |> loop (depth + 1)))
                else None

            derivation |> loop 0


            // iterative deepening
        [4; 10]
            |> Seq.tryPick (fun maxDepth ->
                goalClauses
                    |> Seq.tryPick (fun topClause ->
                        search maxDepth {
                            InputClauses = inputClauses
                            TopClause = topClause
                            DerivedClauses = List.empty
                        }))

type Language =
    {
        Constants : Constant[]
        Functions : Function[]
        Predicates : Predicate[]
    }

module Language =

    let makeParser language : Parser<_> =
        language.Constants
            |> Array.map (fun (Constant name) -> name)
            |> Parser.makeParser

    let tryLinearInductionRaw cnst func premises = function
        | ForAll (variable, schema) ->
            opt {
                let! baseFormula =
                    schema
                        |> Formula.trySubstitute
                            variable
                            (ConstantTerm cnst)
                let! baseDerivation =
                    Derivation.tryProve premises baseFormula

                let! inductiveConclusion =
                    schema
                        |> Formula.trySubstitute
                            variable
                            (Application (
                                func, [| VariableTerm variable |]))
                let inductiveFormula =
                    ForAll (
                        variable,
                        Implication (
                            schema,
                            inductiveConclusion))
                let! inductiveDerivation =
                    let premises' =
                        seq {
                            yield! premises
                            yield baseFormula
                        }
                    Derivation.tryProve premises' inductiveFormula

                return baseDerivation, inductiveDerivation
            }
        | _ -> None

    let tryLinearInduction premises goal language =
        let cnstOpt =
            language.Constants
                |> Seq.tryExactlyOne
        let funcOpt =
            language.Functions
                |> Seq.where (fun (Function (_, arity)) ->
                    arity = 1)
                |> Seq.tryExactlyOne
        match (cnstOpt, funcOpt) with
            | Some cnst, Some func ->
                tryLinearInductionRaw cnst func premises goal
            | _ -> None

