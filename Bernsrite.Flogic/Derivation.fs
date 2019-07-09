namespace Bernsrite.Flogic

/// A resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type Derivation =
    {
        /// Input clauses: premises plus negatated goal.
        InputClauses : Clause[]

        /// Top clause (will be one of the negated goal clauses).
        TopClause : Clause

        /// Clauses derived via linear resolution.
        DerivedClauses : List<Clause>
    }

    /// Steps in this derivation, in order.
    member this.Steps =
        [|
            yield! this.InputClauses
                |> Seq.where (fun clause -> clause <> this.TopClause)
            yield this.TopClause
            yield! this.DerivedClauses
                |> List.rev
        |]

    /// Display string.
    member this.String =
        this.Steps
            |> Seq.mapi (fun index step ->
                sprintf "%d. %A" (index + 1) step)
            |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

/// Proof via resolution.
module Derivation =

    /// Attempts to prove the given goal from the given premises.
    /// http://www.cs.miami.edu/home/geoff/Courses/CSC648-12S/Content/LinearResolution.shtml
    let tryProve premises goal =

        let goalClauses =
            (Not goal)
                |> Clause.toClauses
                |> Seq.toArray
        let inputClauses =
            [|
                yield! premises
                    |> Seq.collect Clause.toClauses
                    |> Seq.toArray
                yield! goalClauses
            |]

        [4; 10]
            |> Seq.tryPick (fun maxDepth ->

                let rec loop depth derivation =
                    if depth < maxDepth then
                        let centerClause =
                            match derivation.DerivedClauses with
                                | head :: _ -> head
                                | [] -> derivation.TopClause
                        Seq.append derivation.InputClauses derivation.DerivedClauses
                            |> Seq.tryPick (fun sideClause ->
                                Clause.resolve centerClause sideClause
                                    |> Seq.tryPick (fun nextCenterClause ->
                                        let nextDerivation =
                                            {
                                                derivation with
                                                    DerivedClauses =
                                                        nextCenterClause
                                                            :: derivation.DerivedClauses
                                            }
                                        if nextCenterClause.Literals.Length = 0 then   // empty clause is a contradiction
                                            Some nextDerivation
                                        else
                                            nextDerivation |> loop (depth + 1)))
                    else None

                goalClauses
                    |> Seq.tryPick (fun topClause ->
                        {
                            InputClauses = inputClauses
                            TopClause = topClause
                            DerivedClauses = List.empty
                        }
                            |> loop 0))
