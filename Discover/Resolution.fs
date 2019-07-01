namespace Discover

module Resolution =

    let rec factor (Clause literals as clause) =
        literals
            |> Seq.toList
            |> List.combinations 2
            |> Seq.tryPick (function
                | (formula1 :: formula2 :: []) ->
                    match Unfiy.tryUnify formula1 formula2 with
                        | Some subs ->
                            let clause' =
                                clause
                                    |> Clause.map (fun literal ->
                                        Substitution.tryApply literal subs
                                            |> Option.map id
                                            |> Option.defaultWith (fun () ->
                                                failwith "Unexpected"))
                            clause'
                                |> factor
                                |> Option.defaultValue clause'
                                |> Some
                        | None -> None
                | _ -> failwith "Unexpected")
