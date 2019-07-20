namespace Bernsrite.Flogic

/// Input to and output of a proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        /// Premises of this proof.
        AnnotatedPremises : (Formula * FormulaRole)[]

        /// Goal of this proof.
        Goal : Formula

        /// Initial clauses (from premises and negated goal)
        AnnotatedInitialClauses : (Clause * ClauseRole)[]

        /// Result of this proof: proved or disproved.
        Result : bool

        /// Derivation of this proof.
        Derivation : LinearResolutionDerivation
    }

    /// Display string.
    member this.ToString(level) =
        seq {

            yield ""
            yield sprintf "Goal: %A" this.Goal |> Print.indent level

            yield ""
            yield "Premises:" |> Print.indent level
            for role, group in this.AnnotatedPremises |> Seq.groupBy snd do
                yield sprintf "%A:" role |> Print.indent (level + 1)
                for premise, _ in group do
                    yield premise |> Print.indent (level + 2)

            yield ""
            yield "Initial clauses:" |> Print.indent level
            for role, group in this.AnnotatedInitialClauses |> Seq.groupBy snd do
                yield sprintf "%A:" role |> Print.indent (level + 1)
                for clause, _ in group do
                    yield clause |> Print.indent (level + 2)

            yield this.Derivation.ToString(level)

            yield ""
            yield if this.Result then "Proved" else "Disproved"
                |> Print.indent level

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module Proof =

    /// Creates a proof.
    let create annotatedPremises goal annotatedInitialClauses result derivation =
        {
            AnnotatedPremises =
                annotatedPremises |> Seq.toArray
            Goal = goal
            AnnotatedInitialClauses =
                annotatedInitialClauses |> Seq.toArray
            Result = result
            Derivation = derivation
        }

    /// Tries to prove the given goal from the given premises.
    let tryProveAnnotated annotatedPremises goal =
    
            // convert premises to clause normal form (CNF)
        let annotatedPremiseClauses =

            let mapTo clauses clauseRole =
                clauses
                    |> Seq.map (fun clause ->
                        clause, clauseRole)

            annotatedPremises
                |> Seq.collect (fun (formula, formulaRole) ->
                    let clauses =
                        formula |> Clause.toClauses
                    seq {
                        match formulaRole with
                            (*
                            | InductionFormula ->
                                let groups =
                                    clauses
                                        |> Seq.groupBy (fun clause ->
                                            clause
                                                |> Clause.toFormula
                                                |> Formula.getFunctions
                                                |> Map.toSeq
                                                |> Seq.sumBy snd)
                                        |> Seq.sortBy fst
                                        |> Seq.map snd
                                        |> Seq.toArray
                                assert(groups.Length = 2)
                                yield! mapTo groups.[0] InductionAntecedentClause
                                yield! mapTo groups.[1] InductionConsequentClause
                            *)
                            | InductionFormula -> yield! mapTo clauses InductionClause
                            | AxiomFormula -> yield! mapTo clauses AxiomClause
                            | GoalFormula -> yield! mapTo clauses GoalClause
                    })
                |> Seq.toArray

            // ensure explicit quantification before negating
        let goal' =
            goal |> Formula.quantifyUniversally

            // annotates the given goal formula as clauses
        let annotateGoal formula =
            formula
                |> Clause.toClauses
                |> Seq.map (fun clause ->
                    clause, GoalClause)
                |> Seq.append annotatedPremiseClauses
                |> Seq.toArray

            // convert goal to CNF for proof
            // proof by refutation: negate goal
        let annotatedProofClauses =
            Not goal' |> annotateGoal

            // convert goal to CNF for disproof
        let annotatedDisproofClauses =
            goal' |> annotateGoal

            // iterative deepening
        [ 5; 7 ]
            |> Seq.collect (fun maxDepth ->
                seq {
                    yield maxDepth, annotatedProofClauses, true
                    yield maxDepth, annotatedDisproofClauses, false
                })
            |> Seq.tryPick (fun (maxDepth, annotatedInitialClauses, flag) ->
                LinearResolution.tryProve maxDepth annotatedInitialClauses
                    |> Option.map (create
                        annotatedPremises
                        goal
                        annotatedInitialClauses
                        flag))

    /// Tries to prove the given goal from the given premises.
    let tryProve premises goal =
        let annotatedPremises =
            premises
                |> Seq.map (fun premise ->
                    premise, AxiomFormula)
        tryProveAnnotated annotatedPremises goal
