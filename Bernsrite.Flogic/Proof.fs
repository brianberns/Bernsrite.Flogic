namespace Bernsrite.Flogic

/// Input to and output of a proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        /// Premises of this proof.
        TaggedPremises : (Formula * Tag)[]

        /// Goal of this proof.
        Goal : Formula

        /// Initial clauses (from premises and negated goal)
        TaggedInitialClauses : (Clause * Tag)[]

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
            for tag, group in this.TaggedPremises |> Seq.groupBy snd do
                yield sprintf "%A:" tag |> Print.indent (level + 1)
                for premise, _ in group do
                    yield premise |> Print.indent (level + 2)

            yield ""
            yield "Initial clauses:" |> Print.indent level
            for tag, group in this.TaggedInitialClauses |> Seq.groupBy snd do
                yield sprintf "%A:" tag |> Print.indent (level + 1)
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
    let create taggedPremises goal taggedInitialClauses result derivation =
        {
            TaggedPremises =
                taggedPremises |> Seq.toArray
            Goal = goal
            TaggedInitialClauses =
                taggedInitialClauses |> Seq.toArray
            Result = result
            Derivation = derivation
        }

    /// Tries to prove the given goal from the given premises.
    let tryProveTagged taggedPremises goal =
    
            // convert premises to clause normal form (CNF)
        let taggedPremiseClauses =
            taggedPremises
                |> Seq.collect (fun (formula, tag) ->
                    formula
                        |> Clause.toClauses
                        |> Seq.map (fun clause ->
                            clause, tag))
                |> Seq.toArray

            // ensure explicit quantification before negating
        let goal' =
            goal |> Formula.quantifyUniversally

            // tags the given goal formula as clauses
        let tagGoal formula =
            formula
                |> Clause.toClauses
                |> Seq.map (fun clause ->
                    clause, Tag.Goal)
                |> Seq.append taggedPremiseClauses
                |> Seq.toArray

            // convert goal to CNF for proof
            // proof by refutation: negate goal
        let taggedProofClauses =
            Not goal' |> tagGoal

            // convert goal to CNF for disproof
        let taggedDisproofClauses =
            goal' |> tagGoal

            // iterative deepening
        [ 5; 7 ]
            |> Seq.collect (fun maxDepth ->
                seq {
                    yield maxDepth, taggedProofClauses, true
                    yield maxDepth, taggedDisproofClauses, false
                })
            |> Seq.tryPick (fun (maxDepth, taggedInitialClauses, flag) ->
                let config =
                    {
                        MaxDepth = maxDepth
                        MaxLiteralCount = 3
                        MaxSymbolCount = 18
                    }
                LinearResolution.tryProve config taggedInitialClauses
                    |> Option.map (create
                        taggedPremises
                        goal
                        taggedInitialClauses
                        flag))

    /// Tries to prove the given goal from the given premises.
    let tryProve premises goal =
        let taggedPremises =
            premises
                |> Seq.map (fun premise ->
                    premise, Tag.Premise)
        tryProveTagged taggedPremises goal
