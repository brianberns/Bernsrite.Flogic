namespace Bernsrite.Flogic

/// One step in a linear resolution derivation.
type LinearResolutionDerivationStep =
    {
        /// Clause created in this step.
        CenterClause : Clause

        /// Existing side clause used in this step's creation.
        SideClause : Clause
    }

/// A linear resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type LinearResolutionDerivation =
    {
        /// Input clauses: premises plus negatated goal.
        InputClauses : Clause[]

        /// Top clause (will be one of the negated goal clauses).
        TopClause : Clause

        /// Derived steps, in reverse order.
        Steps : List<LinearResolutionDerivationStep>
    }

    /// Display string.
    member this.String =
        seq {

            yield "Input clauses:"
            for clause in this.InputClauses do
                yield sprintf "   %A" clause

            let strPairs =
                let steps = this.Steps |> List.rev
                let centerStrs =
                    seq {
                        yield this.TopClause.ToString()
                        for step in steps do
                            yield step.CenterClause.ToString()
                    }
                let sideStrs =
                    seq {
                        for step in steps do
                            yield step.SideClause.ToString()
                        yield ""
                    }
                Seq.zip centerStrs sideStrs
                    |> Seq.toArray

            for i = 0 to strPairs.Length - 1 do
                let centerStr, sideStr = strPairs.[i]
                let prefix = sprintf "%d. %s" (i + 1) centerStr
                yield
                    if i = strPairs.Length - 1 then
                        assert(sideStr = "")
                        prefix
                    else
                        sprintf "%s\twith %s" prefix sideStr

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

type Language =
    {
        Constants : Constant[]
        Functions : Function[]
        Predicates : Predicate[]
    }

module Language =

    /// Creates a parser for the given language.
    let makeParser language : Parser<_> =
        language.Constants
            |> Array.map (fun (Constant name) -> name)
            |> Parser.makeParser

type Proof =
    | LinearResolutionProof of LinearResolutionDerivation
    | LinearInductionProof of (
        Proof (*base case*) * Proof (*induction case*))

module Proof =

    /// Tries to prove the given goal from the given premises via
    /// linear resolution.
    /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
    let tryLinearResolution premises goal =

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
                assert(depth = (derivation.Steps |> Seq.length))
                if depth < maxDepth then

                        // get current center clause
                    let centerClause, centerClauses =
                        match derivation.Steps with
                            | [] ->
                                derivation.TopClause, Seq.empty
                            | step :: steps ->
                                let centerClauses =
                                    steps
                                        |> Seq.map (fun step -> step.CenterClause)
                                step.CenterClause, centerClauses

                        // resolve with all possible side clauses
                    let sideClauses =
                        Seq.append derivation.InputClauses centerClauses
                    sideClauses
                        |> Seq.tryPick (fun sideClause ->
                            Clause.resolve centerClause sideClause
                                |> Seq.tryPick (fun resolvent ->
                                    let nextDerivation =
                                        let step =
                                            {
                                                CenterClause = resolvent
                                                SideClause = sideClause
                                            }
                                        {
                                            derivation with
                                                Steps = step :: derivation.Steps
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
                            Steps = List.empty
                        }))

    /// Tries to prove the given formula using linear induction.
    let private tryLinearInductionRaw constant func premises goal =

        let rec loop premises = function

                // e.g. ∀x.plus(x,0,x)
            | ForAll (variable, schema) as goal ->
                opt {

                        // e.g. plus(0,0,0)
                    let! baseCase =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (ConstantTerm constant)

                        // prove base case
                    let! baseProof =
                        tryProve premises baseCase

                        // e.g. plus(s(x),0,s(x))
                    let! inductiveConclusion =
                        schema
                            |> Formula.trySubstitute
                                variable
                                (Application (
                                    func, [| VariableTerm variable |]))

                        // e.g. plus(x,0,x) ⇒ plus(s(x),0,s(x))
                    let inductiveCase =
                        Implication (
                            schema,
                            inductiveConclusion)

                        // prove inductive case
                    let! inductiveProof =
                        let premises' =
                            seq {
                                yield! premises
                                yield baseCase
                            }
                        tryProve premises' inductiveCase

                    return baseProof, inductiveProof
                }
            | _ -> None

        /// Tries to prove a sub-goal. First via linear resolution, then
        /// via recursive induction.
        and tryProve premises goal =
            goal
                |> tryLinearResolution premises
                |> Option.map LinearResolutionProof
                |> Option.orElseWith (fun () ->
                    goal
                        |> loop premises
                        |> Option.map LinearInductionProof)

        goal |> loop premises

    /// Tries to prove the given formula using linear induction.
    let tryLinearInduction language premises goal =
        let constantOpt =
            language.Constants
                |> Seq.tryExactlyOne
        let functionOpt =
            language.Functions
                |> Seq.where (fun (Function (_, arity)) ->
                    arity = 1)
                |> Seq.tryExactlyOne
        match (constantOpt, functionOpt) with
            | Some constant, Some func ->
                tryLinearInductionRaw constant func premises goal
            | _ -> None

    /// Tries to prove the given formula. First via induction, then
    /// via linear resolution.
    let tryProve language premises goal =
        goal
            |> tryLinearInduction language premises
            |> Option.map LinearInductionProof
            |> Option.orElseWith (fun () ->
                goal
                    |> tryLinearResolution premises
                    |> Option.map LinearResolutionProof)
