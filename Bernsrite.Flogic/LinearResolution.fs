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

    interface IEvidence with

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
                                yield step.SideClause.ToString()
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
        (this :> IEvidence).ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

/// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
module LinearResolution =

    /// Tries to prove the given goal from the given premises via linear
    /// resolution.
    let tryProve premises goal =

            // convert formulas to clauses
        let goalClauses =
            goal
                |> Formula.quantifyUniversally   // must have explicit quantification before negating
                |> Not                           // proof by refutation: negate goal
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

            derivation
                |> loop 0
                |> Option.map (Proof.create premises goal)

            // iterative deepening
        [4; 20]
            |> Seq.tryPick (fun maxDepth ->
                goalClauses
                    |> Seq.tryPick (fun topClause ->
                        search maxDepth {
                            InputClauses = inputClauses
                            TopClause = topClause
                            Steps = List.empty
                        }))
