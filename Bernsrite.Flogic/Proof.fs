namespace Bernsrite.Flogic

/// Input to and output of a proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        /// Premises of this proof.
        AnnotatedPremises : (Formula * ClauseRole)[]

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
            for (premise, role) in this.AnnotatedPremises do
                yield sprintf "%A: %A" premise role
                    |> Print.indent (level + 1)

            yield ""
            yield "Initial clauses:" |> Print.indent level
            for (clause, role) in this.AnnotatedInitialClauses do
                yield sprintf "%A: %A" clause role
                    |> Print.indent (level + 1)

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
            annotatedPremises
                |> Seq.collect (fun (formula, role) ->
                    formula
                        |> Clause.toClauses
                        |> Seq.map (fun clause -> clause, role))
                |> Seq.toArray

            // ensure explicit quantification before negating
        let goal' =
            goal |> Formula.quantifyUniversally

        let annotateGoal formula =
            formula
                |> Clause.toClauses
                |> Seq.map (fun clause ->
                    clause, Goal)
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
                    premise, Axiom)
        tryProveAnnotated annotatedPremises goal
