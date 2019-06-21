namespace Discover

open System

[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Steps : List<InferenceRule * Formula>
        PendingPremises : Set<Formula>
    }

    member this.String =
        let steps =
            this.Steps
                |> List.rev
                |> Seq.map (fun (rule, formula) ->
                    sprintf "%A : %A" formula rule)
        String.Join("\r\n", steps)

    override this.ToString() = this.String

module Proof =

    let empty =
        {
            Steps = List.empty
            PendingPremises = Set.empty
        }

    let private add (rule, formula) proof =
        {
            proof with
                Steps = (rule, formula) :: proof.Steps
                PendingPremises =
                    match rule with
                        | Premise ->
                            proof.PendingPremises.Add(formula)
                        | _ -> proof.PendingPremises
        }

    let addSteps (indexes : _[]) rule consequents proof =

        assert(
            let nRulePremises =
                match rule with
                    | Premise -> 0
                    | Ordinary oir ->
                        oir.Premises.Length
                    | ImplicationIntroduction -> 2
            nRulePremises = indexes.Length)

        let length = proof.Steps.Length
        let antecedents =
            indexes
                |> Array.map (fun idx ->
                    let _, formula =
                        proof.Steps.[length - idx]   // 1-based, from end
                    formula)

        match rule with
            | Premise -> ()
            | _ ->
                let consequentSet =
                    set consequents
                let possibleConsequentSets =
                    rule
                        |> InferenceRule.apply antecedents
                        |> Array.map set
                assert(possibleConsequentSets
                    |> Seq.exists ((=) consequentSet))

        consequents
            |> Seq.map (fun consequent ->
                rule, consequent)
            |> Seq.fold (fun acc step ->
                acc |> add step) proof
