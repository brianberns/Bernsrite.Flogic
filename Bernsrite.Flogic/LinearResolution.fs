namespace Bernsrite.Flogic

open System

module Print =

    /// Indents the given object to the given level.
    let indent level obj =
        sprintf "%s%s"
            (String(' ', 3 * level))
            (obj.ToString())

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
            yield sprintf "Center clause: %A" this.CenterClause
                |> Print.indent level

        } |> String.join "\r\n"

    /// Display string.
    override this.ToString() =
        this.ToString(0)
        
    /// Display string.
    member this.String = this.ToString()

module LinearResolutionDerivation =

    /// Initializes a derivation from the given clauses.
    let create premiseClauses goalClauses topClause =
        assert(goalClauses |> Seq.contains topClause)
        {
            Database =
                [|
                    yield! premiseClauses
                    yield! goalClauses
                |] |> Database.create
            CenterClause = topClause
            Steps = List.empty
        }

/// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
module LinearResolution =
            
    /// Depth-first search.
    let search maxDepth derivation =

        let rec loop depth derivation =
            assert(depth = (derivation.Steps |> Seq.length))
            if depth < maxDepth then

                    // resolve with all possible side clauses
                derivation.Database.Clauses
                    |> Seq.tryPick (fun sideClause ->
                        Clause.resolve derivation.CenterClause sideClause
                            |> Seq.tryPick (fun (resolvent, substitution) ->
                                if resolvent |> Clause.isTautology then
                                    None
                                else
                                    let nextDerivation =
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
                                    if resolvent.Literals.Length = 0 then   // success: empty clause is a contradiction
                                        Some nextDerivation
                                    else
                                        nextDerivation |> loop (depth + 1)))
            else None

        derivation |> loop 0

    /// Tries to prove the given goal from the given premises via linear
    /// resolution.
    let tryProve maxDepth premiseClauses goalClauses =
        goalClauses
            |> Seq.tryPick (fun topClause ->
                LinearResolutionDerivation.create
                    premiseClauses goalClauses topClause
                        |> search maxDepth)
