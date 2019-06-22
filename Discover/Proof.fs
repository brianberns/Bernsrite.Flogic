namespace Discover

open System

/// One step in a proof.
[<StructuredFormatDisplay("{String}")>]
type ProofStep =
    {
        Formula : Formula
        Rule : InferenceRule
        AntecedentIndexes : int[] (*1-based indexes from end of list*)
    }

    /// Display string.
    member this.String =
        sprintf "%A\t\t%A%s%s"
            this.Formula
            this.Rule
            (if this.AntecedentIndexes.Length > 0 then ": " else "")
            (String.Join(", ", this.AntecedentIndexes))

    /// Display string.
    override this.ToString() = this.String

/// A structured proof.
/// http://intrologic.stanford.edu/public/section.php?section=section_04_03
[<StructuredFormatDisplay("{String}")>]
type Proof =
    {
        Steps : List<ProofStep>
        ActiveAssumptionIndexes : List<int>
        ValidAntecedentIndexes : Set<int>
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

    /// An empty proof.
    let empty =
        {
            Steps = List.empty
            ActiveAssumptionIndexes = List.empty
            ValidAntecedentIndexes = Set.empty
        }

    /// Tries to add the given step to the given proof.
    let private tryAdd (formula, rule, antecedentIndexes) proof =

            // validate
        let isValid =
            antecedentIndexes
                |> Array.forall (fun index ->
                    proof.ValidAntecedentIndexes.Contains(index))
                && match rule with
                    | Premise ->
                        proof.ActiveAssumptionIndexes.IsEmpty
                    | ImplicationIntroduction ->
                        (antecedentIndexes |> Array.length = 2)
                            && (antecedentIndexes.[0] = proof.ActiveAssumptionIndexes.Head)
                            && (antecedentIndexes.[1] >= antecedentIndexes.[0])
                    | _ -> true

        if isValid then

                // compute index of this new step
            let index = proof.Steps.Length + 1

            Some {
                proof with

                        // add step
                    Steps =
                        {
                            Formula = formula
                            Rule = rule
                            AntecedentIndexes = antecedentIndexes
                        } :: proof.Steps

                        // push/pop active assumption?
                    ActiveAssumptionIndexes =
                        match rule with

                                // push new active assumption (must be discharged later)
                            | Assumption ->
                                index :: proof.ActiveAssumptionIndexes

                                // discharge active assumption
                            | ImplicationIntroduction ->
                                proof.ActiveAssumptionIndexes.Tail

                                // no-op
                            | _ -> proof.ActiveAssumptionIndexes

                        // prevent future use of completed sub-proof
                    ValidAntecedentIndexes =
                        let indexes =
                            match rule with
                                | ImplicationIntroduction ->
                                    let range = [ antecedentIndexes.[0] .. antecedentIndexes.[1] ]
                                    (proof.ValidAntecedentIndexes, range)
                                        ||> Seq.fold (fun acc index ->
                                            acc.Remove(index))
                                | _ -> proof.ValidAntecedentIndexes
                        indexes.Add(index)
            }

        else None

    module Seq =

        /// Applies a function to each item in a sequence, short-circuiting
        /// if the function fails.
        let tryFold folder state source =
            let folder' stateOpt item =
                stateOpt
                    |> Option.bind (fun state ->
                        folder state item)
            Seq.fold folder' (Some state) source

    /// Tries to add steps to the given proof.
    let tryAddSteps formulas rule (indexes : _[]) proof =

            // validate number of antecedents
        let indexes =
            if rule = ImplicationIntroduction && indexes.Length = 1 then
                [| indexes.[0]; indexes.[0] |]
            else indexes
        let nRulePremises =
            match rule with
                | Premise -> 0
                | Ordinary oir -> oir.Premises.Length
                | Assumption -> 0
                | ImplicationIntroduction -> 2
                | UniversalElimination _ -> 1
        if nRulePremises = indexes.Length then

                // find antecedent formulas
            let antecedents =
                let length = proof.Steps.Length
                indexes
                    |> Array.map (fun index ->
                        let step = proof.Steps.[length - index]
                        step.Formula)

                // ensure that given formulas actually follow from the antecedents
            let isValid =
                match rule with
                    | Premise
                    | Assumption -> true
                    | _ ->
                        let formulaSet = set formulas
                        let possibleFormulaSets =
                            rule
                                |> InferenceRule.apply antecedents
                                |> Array.map set
                        possibleFormulaSets
                            |> Seq.exists ((=) formulaSet)
            if isValid then

                    // attempt to add the given steps to the proof
                formulas
                    |> Seq.tryFold (fun acc formula ->
                        acc |> tryAdd (formula, rule, indexes)) proof

            else None

        else None

    /// Is the given proof complete?
    let isComplete proof =
        proof.Steps.Length > 0
            && proof.ActiveAssumptionIndexes.Length = 0
