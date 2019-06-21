namespace Discover

open System

/// One step in a proof.
[<StructuredFormatDisplay("{String}")>]
type ProofStep =
    {
        Formula : Formula
        Rule : InferenceRule
        Indexes : int[] (*1-based indexes from end of list*)
    }

    /// Display string.
    member this.String =
        sprintf "%A\t\t%A%s%s"
            this.Formula
            this.Rule
            (if this.Indexes.Length > 0 then ": " else "")
            (String.Join(", ", this.Indexes))

    /// Display string.
    override this.ToString() = this.String

/// A structured proof.
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Steps : List<ProofStep>
        PendingPremises : Set<Formula>
    }

    /// Display string.
    member this.String =
        let steps =
            this.Steps
                |> List.rev
                |> Seq.mapi (fun index step ->
                    sprintf "%d. %A" (index + 1) step)
        String.Join("\r\n", steps)

    /// Display string.
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
                Steps =
                    {
                        Formula = formula
                        Rule = rule
                        Indexes = indexes
                    } :: proof.Steps
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
                    let step = proof.Steps.[length - index]
                    step.Formula)

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
