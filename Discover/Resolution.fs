namespace Discover

module Resolution =

    let rec factor (Clause literals as clause) =
        literals
            |> Seq.toList
            |> List.permutations 2
            |> Seq.tryPick (function
                | (formula1 :: formula2 :: []) ->
                    opt {
                        let! subs = Unfiy.tryUnify formula1 formula2
                        return!
                            clause
                                |> Clause.map (fun literal ->
                                    Substitution.tryApply literal subs
                                        |> Option.map id
                                        |> Option.defaultWith (fun () ->
                                            failwith "Unexpected"))
                                |> factor
                    }
                | _ -> failwith "Unexpected")
