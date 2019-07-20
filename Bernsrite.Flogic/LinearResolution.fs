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
        /// Current center clause.
        CenterClause : Clause

        /// Current center clause role.
        CenterClauseRole : ClauseRole

        /// Steps leading to current state, in reverse order.
        Steps : List<LinearResolutionDerivationStep>

        /// Database of active clauses.
        Database : Database
    }

    /// Display string.
    member this.ToString(level) =
        seq {
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
                for (variableName, term) in step.Substitution.Bindings do
                    yield sprintf "%s <- %A" variableName term
                        |> Print.indent (level + 4)

            yield ""
            yield sprintf "Center clause: %A %A" this.CenterClause this.CenterClauseRole
                |> Print.indent level

            yield this.Database.ToString(level + 1)

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module LinearResolutionDerivation =

    /// Creates a derivation for the given clauses.
    let create annotatedClauses topClause =
        assert(
            annotatedClauses
                |> Seq.map fst
                |> Seq.contains topClause)
        {
            Database = Database.create annotatedClauses
            CenterClause = topClause
            CenterClauseRole = Goal
            Steps = List.empty
        }

    /// Initializes derivations for the given clauses.
    let generate annotatedClauses =
        [|
            for (clause, role) in annotatedClauses do
                if role = Goal then
                    yield create annotatedClauses clause
        |]

/// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
module LinearResolution =
            
    /// Depth-first search.
    let search maxDepth derivation =

        let rec loop depth derivation =
            assert(depth = (derivation.Steps |> Seq.length))
            if depth < maxDepth then

                    // resolve with all possible side clauses
                derivation.Database
                    |> Database.getPossibleResolutionClauses derivation.CenterClauseRole
                    |> Seq.tryPick (fun sideClause ->
                        Clause.resolve derivation.CenterClause sideClause
                            |> Seq.tryPick (fun (resolvent, substitution) ->
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
                                                    |> Database.add resolvent Axiom
                                    }
                                if resolvent.IsEmpty then   // success: empty clause is a contradiction
                                    Some derivation'
                                else
                                    derivation' |> loop (depth + 1)))
            else None

        derivation |> loop 0

    /// Tries to prove the given goal from the given premises via linear
    /// resolution.
    let tryProve maxDepth annotatedClauses =
        LinearResolutionDerivation.generate annotatedClauses
                |> Seq.tryPick (search maxDepth)
