namespace Discover

type ProofStep =
    Option<InferenceRule> * Formula

type Proof =
    {
        Steps : List<ProofStep>
        PendingPremises : Set<Formula>
    }

module Proof =

    let empty =
        {
            Steps = List.empty
            PendingPremises = Set.empty
        }

    let private add (ruleOpt, formula) proof =
        {
            proof with
                Steps = (ruleOpt, formula) :: proof.Steps
                PendingPremises =
                    if ruleOpt.IsSome then
                        proof.PendingPremises
                    else
                        proof.PendingPremises.Add(formula)
        }

    let addSteps (indexes : _[]) ruleOpt consequents proof =

        assert(
            let nRulePremises =
                ruleOpt
                    |> Option.map (fun rule ->
                        rule.Premises.Length)
                    |> Option.defaultValue 0
            nRulePremises = indexes.Length)

        let length = proof.Steps.Length
        let antecedents =
            indexes
                |> Array.map (fun idx ->
                    let _, formula =
                        proof.Steps.[length - idx]   // 1-based, from end
                    formula)

        match ruleOpt with
            | Some rule ->
                let consequentSet =
                    set consequents
                let possibleConsequentSets =
                    rule
                        |> InferenceRule.apply antecedents
                        |> Array.map set
                assert(possibleConsequentSets
                    |> Seq.exists ((=) consequentSet))
            | None -> ()

        consequents
            |> Seq.map (fun consequent ->
                ruleOpt, consequent)
            |> Seq.fold (fun acc step ->
                acc |> add step) proof
