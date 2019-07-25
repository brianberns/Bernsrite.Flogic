namespace Bernsrite.Flogic

/// Input to and output of a proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        /// Premises of this proof.
        Premises : Formula[]

        /// Goal of this proof.
        Goal : Formula

        /// Initial clauses (from premises and negated goal)
        InitialClauses : Clause[]

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
            for premise in this.Premises  do
                yield premise |> Print.indent (level + 1)

            yield ""
            yield "Initial clauses:" |> Print.indent level
            for clause in this.InitialClauses do
                yield clause |> Print.indent (level + 1)

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
    let create premises goal initialClauses result derivation =
        {
            Premises = premises |> Seq.toArray
            Goal = goal
            InitialClauses = initialClauses |> Seq.toArray
            Result = result
            Derivation = derivation
        }

    /// Tries to prove the given goal from the given premises.
    let tryProve premises goal =
    
            // convert premises to clause normal form (CNF)
        let premiseClauses =
            premises
                |> Seq.collect Clause.toClauses
                |> Seq.toArray

            // ensure explicit quantification before negating
        let goal' =
            goal |> Formula.quantifyUniversally

            // convert goal to CNF for proof
            // proof by refutation: negate goal
        let proofGoalClauses =
            Not goal' |> Clause.toClauses

            // convert goal to CNF for disproof
        let disproofGoalClauses =
            goal' |> Clause.toClauses

            // iterative deepening
        [ 5; 7 ]
            |> Seq.collect (fun maxDepth ->
                seq {
                    yield maxDepth, proofGoalClauses, true
                    yield maxDepth, disproofGoalClauses, false
                })
            |> Seq.tryPick (fun (maxDepth, goalClauses, flag) ->
                let config =
                    {
                        MaxDepth = maxDepth
                        MaxLiteralCount = 3
                        MaxSymbolCount = 18
                    }
                LinearResolution.tryProve config premiseClauses goalClauses
                    |> Option.map (fun derivation ->
                        let initialClauses =
                            Seq.append premiseClauses goalClauses
                        create premises goal initialClauses flag derivation))
