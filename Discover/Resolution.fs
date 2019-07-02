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

    /// Reduces the given clause to its smallest factor.
    let private factor clause =

        let rec loop (Clause literals as clause) =
            literals
                |> Seq.toList
                |> List.combinations 2
                |> Seq.tryPick (function

                        // try to unify each pair of literals in the clause
                    | (literal1 :: literal2 :: []) ->
                        Unfiy.tryUnify literal1 literal2
                            |> Option.map (fun subs ->

                                    // reduce the entire clause using the successful substitution
                                    // and recurse to see if further factoring is possible
                                clause
                                    |> Clause.map (
                                        Substitution.applyLiteral subs)
                                    |> loopDefault)

                    | _ -> failwith "Unexpected")

        and loopDefault clause =
            clause
                |> loop
                |> Option.defaultValue clause

        clause |> loopDefault

    /// Derives a conclusion from the given clauses using the resolution
    /// principle.
    let resolve clause1 clause2 =

        let (Clause literals1) as clause1' =
            clause1 |> factor
        let (Clause literals2) =
            clause2
                |> deconflict clause1'
                |> factor

        let extract = function
            | LiteralAtom _ as literal ->
                literal, 1
            | LiteralNot predTerms ->
                Formula predTerms |> Literal.ofFormula, -1

        seq {
            for literal1 in literals1 do
                let others1Lazy = lazy literals1.Remove(literal1)
                for literal2 in literals2 do
                    match extract literal1, extract literal2 with
                        | (lit1, sign1), (lit2, sign2) when sign1 <> sign2 ->
                            match Unfiy.tryUnify lit1 lit2 with
                                | Some subs ->
                                    let others2 = literals2.Remove(literal2)
                                    yield Seq.append others1Lazy.Value others2
                                        |> Seq.map (Substitution.applyLiteral subs)
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
        Steps : List<Clause>
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

module Derivation =

    let extend derivation =

        let combinations =
            derivation.Steps
                |> List.combinations 2
        seq {
            for combination in combinations do
                let nextSteps =
                    match combination with
                        | stepA :: stepB :: [] ->
                            Resolution.resolve stepA stepB
                        | _ -> failwith "Unexpected"
                for step in nextSteps do
                    yield {
                        Steps = step :: derivation.Steps
                    }
        }

    let prove premises goal =

        let derivation =
            {
                Steps =
                    seq {
                        for premise in premises do
                            yield! premise |> Clause.toClauses
                        yield! (Not goal) |> Clause.toClauses
                    }
                        |> Seq.rev
                        |> Seq.toList
            }
        if derivation.Steps.IsEmpty then
            failwith "No premises"

        [1 .. 10]
            |> Seq.tryPick (fun maxDepth ->

                let rec loop depth derivation =
                    if depth >= maxDepth then None
                    else
                        derivation
                            |> extend
                            |> Seq.tryPick (fun deriv ->
                                let (Clause literals) = deriv.Steps.Head
                                if literals.IsEmpty then
                                    Some deriv
                                else
                                    deriv |> loop (depth + 1))

                derivation |> loop 0)
