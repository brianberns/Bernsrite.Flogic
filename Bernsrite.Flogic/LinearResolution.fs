namespace Bernsrite.Flogic

/// One step in a linear resolution derivation.
type LinearResolutionDerivationStep =
    {
        /// Clause used in this step.
        CenterClause : Clause

        /// Side clause used in this step.
        SideClause : Clause

        /// Substitution used in this step.
        Substitution : Substitution
    }

/// A linear resolution derivation.
[<StructuredFormatDisplay("{String}")>]
type LinearResolutionDerivation =
    {
        /// Initial clauses (from premises and negated goal)
        InitialClauses : Clause[]

        /// Current center clause.
        CenterClause : Clause

        /// Steps leading to current state, in reverse order.
        Steps : List<LinearResolutionDerivationStep>

        /// Database of active clauses.
        Database : Database
    }

    /// Display string.
    member this.ToString(level) =
        seq {
            yield ""
            yield "Initial clauses:" |> Print.indent level
            for clause in this.InitialClauses do
                yield clause |> Print.indent (level + 1)

            yield ""
            yield "Steps:" |> Print.indent level
            let steps =
                this.Steps
                    |> List.rev
                    |> Seq.toArray
            for i = 0 to steps.Length - 1 do
                let step = steps.[i]
                yield ""
                yield sprintf "%d. %A" (i + 1) step.CenterClause
                    |> Print.indent (level + 1)
                yield sprintf "with %A" step.SideClause
                    |> Print.indent (level + 3)
                for variableName, term in step.Substitution.Bindings do
                    yield sprintf "%s <- %A" variableName term
                        |> Print.indent (level + 4)

            yield ""
            yield sprintf "Center clause: %A" this.CenterClause
                |> Print.indent level

            yield this.Database.ToString(level + 1)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

    /// Printable implementation.
    member this.Printable =
        { ToString = this.ToString }

/// Restrictions to avoid runaway search.
type LinearResolutionConfiguration =
    {
        /// Maximum depth of the search tree.
        MaxDepth : int

        /// Maximum # of literals in a clause.
        MaxLiteralCount : int

        /// Maximum # of symbols in a clause.
        MaxSymbolCount : int
    }

module LinearResolutionDerivation =

    /// Creates a derivation for the given clauses.
    let create clauses topClause =
        assert(clauses |> Seq.contains topClause)
        {
            InitialClauses = clauses
            Database = Database.create clauses
            CenterClause = topClause
            Steps = List.empty
        }

    /// Initializes derivations for the given clauses.
    let generate premiseClauses goalClauses =
        let allClauses =
            Seq.append premiseClauses goalClauses
                |> Seq.toArray

            // guess that negative clauses are more likely to lead to contradiction
        goalClauses
            |> Seq.sortBy (fun clause ->
                clause.Literals
                    |> Seq.where (fun literal ->
                        literal.IsPositive)
                    |> Seq.length)
            |> Seq.map (fun topClause ->
                create allClauses topClause)

/// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
module LinearResolution =
            
    /// Depth-first search.
    let search config derivation =

        let rec loop depth derivation =
            assert(depth = (derivation.Steps |> Seq.length))
            if depth < config.MaxDepth then

                    // resolve with all possible side clauses
                derivation.Database.Clauses
                    |> Seq.tryPick (fun sideClause ->
                        Clause.resolve derivation.CenterClause sideClause
                            |> Seq.tryPick (fun (resolvent, substitution) ->
                                if resolvent.Literals.Count > config.MaxLiteralCount
                                    || resolvent.SymbolCount > config.MaxSymbolCount then
                                    None
                                elif derivation.Database.Clauses |> Seq.contains resolvent then
                                    None
                                else
                                    let derivation' =
                                        {
                                            derivation with
                                                CenterClause = resolvent
                                                Steps =
                                                    {
                                                        CenterClause = derivation.CenterClause
                                                        SideClause = sideClause
                                                        Substitution = substitution
                                                    } :: derivation.Steps
                                                Database =
                                                    derivation.Database
                                                        |> Database.add resolvent
                                        }
                                    if resolvent.IsEmpty then   // success: empty clause is a contradiction
                                        Some derivation'
                                    else
                                        derivation' |> loop (depth + 1)))
            else None

        derivation |> loop 0

    /// Tries to derive the given goal from the given premises.
    let private tryDerive limits premiseClauses goalClauses =
        LinearResolutionDerivation.generate premiseClauses goalClauses
            |> Seq.tryPick (search limits)

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
        [ 1; 3; 5; 7 ]
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
                        MaxSymbolCount = 15
                    }
                opt {
                    let! derivation = tryDerive config premiseClauses goalClauses
                    return Proof.create premises goal flag derivation.Printable
                })
