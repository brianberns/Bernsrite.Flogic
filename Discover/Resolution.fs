namespace Discover

module Resolution =

    let deconflictClause (Clause literalsKeep) clauseRename =
        let seen =
            seq {
                for literal in literalsKeep do
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
            Formula (predicate, terms)
                |> constructor
                |> Literal.ofFormula

        clauseRename
            |> Clause.map (function
                | LiteralAtom (predicate, terms) ->
                    deconflictPredicate predicate terms id
                | LiteralNot (predicate, terms) ->
                    deconflictPredicate predicate terms Not)

    /// Reduces the given clause to its smallest factor.
    let rec factor (Clause literals as clause) =
        literals
            |> Seq.toList
            |> List.combinations 2
            |> Seq.tryPick (function

                    // try to unify each pair of literals in the clause
                | (literal1 :: literal2 :: []) ->
                    match Unfiy.tryUnify literal1 literal2 with
                        | Some subs ->

                                // reduce the entire clause using the successful substitution
                            let clause' =
                                clause
                                    |> Clause.map (
                                        Substitution.applyLiteral subs)

                                // recurse to see if further factoring is possible
                            clause'
                                |> factor
                                |> Option.defaultValue clause'
                                |> Some

                        | None -> None

                | _ -> failwith "Unexpected")
