namespace Discover

/// http://fssnip.net/6C/title/Permutation-and-Combination
module List =

    type ListBuilder() =
      let concatMap f m = List.concat( List.map (fun x -> f x) m )
      member this.Bind (m, f) = concatMap (fun x -> f x) m 
      member this.Return (x) = [x]
      member this.ReturnFrom (x) = x
      member this.Zero () = []
      member this.Combine (a,b) = a@b
      member this.Delay f = f ()

    let list = ListBuilder()

    let rec permutations n lst = 
      let rec selections = function
          | []      -> []
          | x::xs -> (x,xs) :: list { let! y,ys = selections xs 
                                      return y,x::ys }
      (n, lst) |> function
      | 0, _ -> [[]]
      | _, [] -> []
      | _, x::[] -> [[x]]
      | n, xs -> list { let! y,ys = selections xs
                        let! zs = permutations (n-1) ys 
                        return y::zs }

    let rec combinations n lst = 
      let rec findChoices = function 
        | []    -> [] 
        | x::xs -> (x,xs) :: list { let! y,ys = findChoices xs 
                                    return y,ys } 
      list { if n = 0 then return! [[]]
             else
               let! z,r = findChoices lst
               let! zs = combinations (n-1) r 
               return z::zs }
