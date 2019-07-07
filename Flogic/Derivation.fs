namespace Flogic

/// A resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type Derivation =
    {
        Premises : Clause[]
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

    /// Generates all possible extensions of the given derivation
    /// via resolution.
    let private extend (derivation : Derivation) =

        let supportSteps =
            derivation.Support
                |> Seq.toArray
        let allSteps =
            Seq.append derivation.Support derivation.Premises
                |> Seq.toArray
        [|
            for iSupport = 0 to supportSteps.Length - 1 do
                for iAll = iSupport + 1 to allSteps.Length - 1 do
                    yield supportSteps.[iSupport], allSteps.[iAll]
        |]
            |> Array.Parallel.collect (fun (supportStep, allStep) ->
                [|
                    for nextStep in Clause.resolve supportStep allStep do
                        yield {
                            derivation with
                                Support = nextStep :: derivation.Support
                        }
                |])

    /// Attempts to prove the given goal from the given premises.
    let tryProve maxDepths premises goal =

            // initialize derivation
        let derivation =
            {
                Premises =
                    premises
                        |> Seq.collect Clause.toClauses
                        |> Seq.toArray
                Support =
                    (Not goal)
                        |> Clause.toClauses
                        |> Seq.toList
            }

            // iterative deepening
        maxDepths
            |> Seq.tryPick (fun maxDepth ->

                let rec loop depth derivation =
                    if depth >= maxDepth then None
                    else
                        derivation
                            |> extend
                            |> Seq.tryPick (fun deriv ->
                                if deriv.Support.Head.Literals.Length = 0 then
                                    Some deriv
                                else
                                    deriv |> loop (depth + 1))

                derivation |> loop 0)
