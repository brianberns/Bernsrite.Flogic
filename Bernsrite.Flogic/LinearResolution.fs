namespace Bernsrite.Flogic

/// One step in a linear resolution derivation.
type LinearResolutionDerivationStep =
    {
        /// Clause created in this step.
        CenterClause : Clause

        /// Existing side clause used in this step's creation.
        SideClause : Clause

        /// Substitution used in this step's creation.
        Substitution : Substitution
    }

/// A linear resolution derivation.
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
    member this.ToString(level) =
        seq {

            yield ""
            yield "Input clauses:" |> Print.indent level
            for clause in this.InputClauses do
                yield clause |> Print.indent (level + 1)

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
                            yield sprintf "%A via %A" step.SideClause step.Substitution
                        yield ""
                    }
                Seq.zip centerStrs sideStrs
                    |> Seq.toArray

            yield ""
            yield "Steps:" |> Print.indent level
            for i = 0 to strPairs.Length - 1 do
                let centerStr, sideStr = strPairs.[i]
                let prefix = sprintf "%d. %s" (i + 1) centerStr
                let str =
                    if i = strPairs.Length - 1 then
                        assert(sideStr = "")
                        prefix
                    else
                        sprintf "%s with %s" prefix sideStr
                yield str |> Print.indent (level + 1)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

    /// Printable implementation.
    member this.Printable =
        {
            Object = this
            ToString = this.ToString
        }

module LinearResolutionDerivation =

    /// Initializes a derivation from the given clauses.
    let create premiseClauses goalClauses topClause =
        assert(goalClauses |> Seq.contains topClause)
        {
            InputClauses =
                [|
                    yield! premiseClauses
                    yield! goalClauses
                |]
            TopClause = topClause
            Steps = List.empty
        }

/// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
module LinearResolution =
            
    /// Depth-first search.
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
                            |> Seq.tryPick (fun (resolvent, substitution) ->
                                if resolvent |> Clause.isTautology then
                                    None
                                else
                                    let nextDerivation =
                                        let step =
                                            {
                                                CenterClause = resolvent
                                                SideClause = sideClause
                                                Substitution = substitution
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

    /// Tries to prove the given goal from the given premises via linear
    /// resolution.
    let tryProve language premises goal =

            // convert premises to clause normal form (CNF)
        let premiseClauses =
            [|
                yield! premises
                yield! Language.generateAxioms language goal
            |]
                |> Seq.collect Clause.toClauses
                |> Seq.toArray

            // ensure explicit quantification before negating
        let goal' =
            goal |> Formula.quantifyUniversally

            // convert goal to CNF for proof
        let proofGoalClauses =
            goal'
                |> Not   // proof by refutation: negate goal
                |> Clause.toClauses
                |> Seq.toArray

            // convert goal to CNF for disproof
        let disproofGoalClauses =
            goal'
                |> Clause.toClauses
                |> Seq.toArray

            // iterative deepening
        [ 4; 10 ]
            |> Seq.collect (fun maxDepth ->
                seq {
                    yield maxDepth, proofGoalClauses, true
                    yield maxDepth, disproofGoalClauses, false
                })
            |> Seq.tryPick (fun (maxDepth, goalClauses, flag) ->
                goalClauses
                    |> Seq.tryPick (fun topClause ->
                        LinearResolutionDerivation.create
                            premiseClauses goalClauses topClause
                                |> search maxDepth)
                    |> Option.map (fun derivation ->
                        Proof.create
                            premises
                            goal
                            flag
                            derivation.Printable))
