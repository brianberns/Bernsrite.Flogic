namespace Discover

module Resolution =

    /// Reduces the given clause to its smallest factor.
    let rec factor (Clause literals as clause) =
        literals
            |> Seq.toList
            |> List.combinations 2
            |> Seq.tryPick (function

                    // try to unify each pair of literals in the clause
                | ((Literal formula1) :: (Literal formula2) :: []) ->
                    match Unfiy.tryUnify formula1 formula2 with
                        | Some subs ->

                                // reduce the entire clause using the successful substitution
                            let clause' =
                                clause
                                    |> Clause.map (fun (Literal formula) ->
                                        Substitution.tryApply formula subs
                                            |> Option.map Literal.ofFormula
                                            |> Option.defaultWith (fun () ->
                                                failwith "Unexpected"))

                                // recurse to see if further factoring is possible
                            clause'
                                |> factor
                                |> Option.defaultValue clause'
                                |> Some

                        | None -> None

                | _ -> failwith "Unexpected")
