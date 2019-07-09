namespace Bernsrite.Flogic

/// A resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type Derivation =
    {
        /// Starting premises.
        Premises : Clause[]

        /// Support steps derived so far, in reverse order.
        Support : List<Clause>
    }

    /// Display string.
    member this.String =

            // steps in this derivation, in order
        seq {
            yield! this.Premises
            yield! this.Support |> List.rev
        }
            |> Seq.mapi (fun index step ->
                sprintf "%d. %A" (index + 1) step)
            |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

/// Proof via resolution.
module Derivation =

    /// Searches for a contradiction reachable from the given derivation.
    let private searchContradiction maxDepth (derivation : Derivation) =

        let rec loop depth derivation =
            if depth < maxDepth then
                let pairs =
                    let supportSteps =
                        derivation.Support
                            |> Seq.toArray
                    seq {
                        for iSupport = 0 to 0 (*supportSteps.Length - 1*) do
                            for premise in derivation.Premises do
                                yield supportSteps.[iSupport], premise
                            (*
                            for jSupport = iSupport - 1 downto 0 do
                                yield supportSteps.[iSupport], supportSteps.[jSupport]
                            *)
                    }
                pairs
                    |> Seq.tryPick (fun (step1, step2) ->
                        Clause.resolve step1 step2
                            |> Seq.tryPick (fun nextStep ->
                                let nextDerivation =
                                    {
                                        derivation with
                                            Support = nextStep :: derivation.Support
                                    }
                                if nextStep.Literals.Length = 0 then   // empty clause is a contradiction
                                    Some nextDerivation
                                else
                                    nextDerivation |> loop (depth + 1)))
            else None

        derivation |> loop 0

    /// Attempts to prove the given goal from the given premises.
    let tryProve premises goal =
        {
            Premises =
                premises
                    |> Seq.collect Clause.toClauses
                    |> Seq.toArray
            Support =
                (Not goal)
                    |> Clause.toClauses
                    |> Seq.toList
        } |> searchContradiction 10
