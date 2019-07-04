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
                    match literal with
                        | LiteralAtom (_, terms) ->
                            for term in terms do
                                yield! term |> Term.getVariables
                        | LiteralNot (_, terms) ->
                            for term in terms do
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

        let deconflictPredicate predicate terms constructor =
            let terms' =
                terms |> Array.map deconflictTerm
            Formula (predicate, terms')
                |> constructor
                |> Literal.ofFormula

            // rename variables used in the second clause as needed
        clauseToRename
            |> Clause.map (function
                | LiteralAtom (predicate, terms) ->
                    deconflictPredicate predicate terms id
                | LiteralNot (predicate, terms) ->
                    deconflictPredicate predicate terms Not)

    /// Answers all factors of the given clause (including itself).
    let rec private getFactors (Clause literals as clause) =
        let combinations =
            literals
                |> Seq.toList
                |> List.combinations 2
        seq {
            yield clause
            for combination in combinations do
                match combination with
                    | (literal1 :: literal2 :: []) ->
                        match Unfiy.tryUnify literal1 literal2 with
                            | Some subst ->
                                yield! clause
                                    |> Clause.map (
                                        Substitution.applyLiteral subst)
                                    |> getFactors
                            | None -> ()
                    | _ -> failwith "Unexpected"
        }        

    /// Derives a conclusion from the given clauses using the resolution
    /// principle.
    let resolve clause1 clause2 =

        let clause2 = deconflict clause1 clause2

        let clauses1 = clause1 |> getFactors
        let clauses2 = clause2 |> getFactors

        let extract = function
            | LiteralAtom _ as literal ->
                literal, 1
            | LiteralNot predTerms ->
                Formula predTerms |> Literal.ofFormula, -1

        seq {
            for (Clause literals1) in clauses1 do
                for (Clause literals2) in clauses2 do
                    for literal1 in literals1 do
                        let others1Lazy = lazy literals1.Remove(literal1)
                        for literal2 in literals2 do
                            match extract literal1, extract literal2 with
                                | (lit1, sign1), (lit2, sign2) when sign1 <> sign2 ->
                                    match Unfiy.tryUnify lit1 lit2 with
                                        | Some subst ->
                                            let others2 = literals2.Remove(literal2)
                                            yield Seq.append others1Lazy.Value others2
                                                |> Seq.map (Substitution.applyLiteral subst)
                                                |> set
                                                |> Clause
                                        | None -> ()
                                | _ -> ()
        } |> set

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
