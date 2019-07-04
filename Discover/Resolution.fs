namespace Discover

open System

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

    /// Answers all factors of the given clause (including itself).
    let private getFactors clause =

        let rec loop (Clause literals as clause) =
            seq {
                yield clause
                for literal1 in literals do
                    for literal2 in literals do
                        if literal1 <> literal2 then
                            match Unfiy.tryUnify literal1 literal2 with
                                | Some subst ->
                                    yield! clause
                                        |> Clause.map (
                                            Substitution.applyLiteral subst)
                                        |> loop
                                | None -> ()
            }

        clause
            |> loop
            |> Seq.toArray

    /// Derives a conclusion from the given clauses using the resolution
    /// principle.
    let resolve clause1 clause2 =

        let clauses1 =
            clause1 |> getFactors
        let clauses2 =
            deconflict clause1 clause2 |> getFactors
        let clausePairs =
            [|
                for clause1' in clauses1 do
                    for clause2' in clauses2 do
                        yield clause1', clause2'
            |]

        clausePairs
            |> Array.Parallel.collect (fun (Clause literals1, Clause literals2) ->
                [|
                    for literal1 in literals1 do
                        let others1Lazy = lazy literals1.Remove(literal1)
                        for literal2 in literals2 do
                            match Unfiy.tryUnify literal1 literal2 with
                                | Some subst ->
                                    let others2 = literals2.Remove(literal2)
                                    yield Seq.append others1Lazy.Value others2
                                        |> Seq.map (Substitution.applyLiteral subst)
                                        |> set
                                        |> Clause
                                | None -> ()
                |])
            |> set

/// A resolution derivation.
/// http://intrologic.stanford.edu/public/section.php?section=section_05_04
[<StructuredFormatDisplay("{String}")>]
type Derivation =
    {
        Premises : Clause[]
        Support : List<Clause>
    }

    /// Steps in this derivation, in order.
    member this.Steps =
        [|
            yield! this.Premises
            yield! this.Support |> List.rev
        |]

    /// Display string.
    member this.String =
        this.Steps
            |> Seq.mapi (fun index step ->
                sprintf "%d. %A" (index + 1) step)
            |> String.join "\r\n"

    /// Display string.
    override this.ToString() = this.String

module Derivation =

    let private extend (derivation : Derivation) =

        seq {
            for support in derivation.Support do
                for any in derivation.Steps do
                    if support <> any then
                        for step in Resolution.resolve support any do
                            yield {
                                derivation with
                                    Support = step :: derivation.Support
                            }
        }

    let prove premises goal =

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

        [1 .. 10]
            |> Seq.tryPick (fun maxDepth ->
                printfn "maxDepth: %A" maxDepth
                let rec loop depth derivation =
                    if depth >= maxDepth then None
                    else
                        derivation
                            |> extend
                            |> Seq.tryPick (fun deriv ->
                                let (Clause literals) = deriv.Support.Head
                                if literals.IsEmpty then
                                    Some deriv
                                else
                                    deriv |> loop (depth + 1))

                derivation |> loop 0)
