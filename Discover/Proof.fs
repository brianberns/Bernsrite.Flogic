namespace Discover

open System

[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Steps : List<Formula * InferenceRule * int[] (*1-based indexes from end of list*)>
        PendingPremises : Set<Formula>
    }

    member this.String =
        let steps =
            this.Steps
                |> List.rev
                |> Seq.mapi (fun index (formula, rule, indexes) ->
                    sprintf "%d. %A\t\t%A%s%s"
                        (index + 1)
                        formula
                        rule
                        (if indexes.Length > 0 then ": " else "")
                        (String.Join(", ", indexes)))
        String.Join("\r\n", steps)

    override this.ToString() = this.String

module Proof =

    let empty =
        {
            Steps = List.empty
            PendingPremises = Set.empty
        }

    let private add (formula, rule, indexes) proof =
        {
            proof with
                Steps = (formula, rule, indexes) :: proof.Steps
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
                    | Assumption -> 0
                    | ImplicationIntroduction -> 2
            nRulePremises = indexes.Length)

        let length = proof.Steps.Length
        let antecedents =
            indexes
                |> Array.map (fun index ->
                    let formula, _, _ =
                        proof.Steps.[length - index]
                    formula)

        match rule with
            | Premise
            | Assumption -> ()
            | Ordinary _
            | ImplicationIntroduction ->
                let consequentSet =
                    set consequents
                let possibleConsequentSets =
                    rule
                        |> InferenceRule.apply antecedents
                        |> Array.map set
                assert(possibleConsequentSets
                    |> Seq.exists ((=) consequentSet))

        consequents
            |> Seq.fold (fun acc consequent ->
                acc |> add (consequent, rule, indexes)) proof
