namespace Discover

/// Inference using the resolution principle.
module Resolution =

    /// Deconflicts variable names in the given clauses by renaming
    /// variables in the second clause as needed.
    let private deconflict (Clause literalsToKeep) clauseToRename =

            // find all variables used in the first clause
        let seen =
            seq {
                for literal in literalsToKeep do
                    for term in literal.Terms do
                        yield! term |> Term.getVariables
            } |> set

        let deconflictVariable variable =
            variable
                |> Variable.deconflict seen
                |> fst

        let rec deconflictTerm = function
            | Term variable ->
                variable
                    |> deconflictVariable
                    |> Term
            | Application (func, terms) ->
                Application (
                    func,
                    terms |> Array.map deconflictTerm)

            // rename variables used in the second clause as needed
        clauseToRename
            |> Clause.map (Literal.map deconflictTerm)

    /// Applies the given substitution to the given literal.
    let private apply subst literal =
        if subst.SubstMap.Length = 0 then
            literal
        else
            literal |> Literal.map (Substitution.applyTerm subst)

    /// Answers all factors of the given clause (including itself).
    let private getAllFactors clause =

        let rec loop (Clause literals as clause) =
            seq {
                yield clause
                for i = 0 to literals.Length - 1 do
                    for j = 0 to literals.Length - 1 do
                        if i <> j then
                            match Literal.tryUnify literals.[i] literals.[j] with
                                | Some subst ->
                                    yield! clause
                                        |> Clause.map (apply subst)
                                        |> loop
                                | None -> ()
            }

        clause
            |> loop
            |> Seq.toArray

    /// Derives a new clause from the given clauses using the resolution
    /// principle.
    let resolve clause1 clause2 =

            // isolates each item in the given array
        let createAllButArray mapping (items : _[]) =
            items
                |> Array.mapi (fun i item ->
                    let item' = mapping item
                    let allBut =
                        lazy [|
                            for j = 0 to items.Length - 1 do
                                if i <> j then
                                    yield items.[j]
                        |]
                    item', allBut)

            // deconflict the clauses and find all factors of each one
        let allButArrays1 =
            clause1
                |> getAllFactors
                |> Seq.map (fun (Clause literals) ->
                    literals
                        |> createAllButArray id)
        let allButArrays2 =
            deconflict clause1 clause2
                |> getAllFactors
                |> Seq.map (fun (Clause literals) ->
                    literals
                        |> createAllButArray Literal.negate)   // negate for unification

        [|
            for allButArray1 in allButArrays1 do
                for allButArray2 in allButArrays2 do
                    for (literal1, allBut1) in allButArray1 do
                        for (literal2, allBut2) in allButArray2 do
                            match Literal.tryUnify literal1 literal2 with
                                | Some subst ->
                                    yield Seq.append allBut1.Value allBut2.Value
                                        |> Seq.map (apply subst)
                                        |> Clause.create
                                | None -> ()
        |] |> set

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
                    for nextStep in Resolution.resolve supportStep allStep do
                        yield {
                            derivation with
                                Support = nextStep :: derivation.Support
                        }
                |])

    /// Attempts to prove the given goal from the given premises.
    let prove maxDepths premises goal =

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
                                let (Clause literals) = deriv.Support.Head
                                if literals.Length = 0 then
                                    Some deriv
                                else
                                    deriv |> loop (depth + 1))

                derivation |> loop 0)
