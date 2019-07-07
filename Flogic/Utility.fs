namespace Flogic

open System

/// http://fssnip.net/6C/title/Permutation-and-Combination
module List =

    type ListBuilder() =
        member __.Bind(lst, f) = List.collect f lst
        member __.Return(x) = [x]
        member __.ReturnFrom(x) = x
        member __.Zero() = []
        member __.Combine(a, b) = a @ b
        member __.Delay(f) = f ()

    let list = ListBuilder()

    /// Permutations of N items taken from the given list.
    let rec permutations n lst = 

        let rec selections = function
            | [] -> []
            | x::xs ->
                (x, xs) :: list {
                    let! y, ys = selections xs 
                    return y, x::ys
                }

        match (n, lst) with
            | 0, _ -> [[]]
            | _, [] -> []
            | _, x::[] -> [[x]]
            | n, xs ->
                list {
                    let! y, ys = selections xs
                    let! zs = permutations (n-1) ys 
                    return y::zs
                }

    /// Combinations of N items taken from the given list.
    let rec combinations n lst = 

        let rec findChoices = function 
            | [] -> [] 
            | x::xs ->
                (x, xs) :: list {
                    let! y, ys = findChoices xs
                    return y, ys
                }

        list {
            if n = 0 then return! [[]]
            else
                let! z, r = findChoices lst
                let! zs = combinations (n-1) r 
                return z::zs
        }

    /// http://www.fssnip.net/2A/title/Cartesian-product-of-n-lists
    /// Takes an input like [[1;2;5]; [3;4]; [6;7]] and returns
    /// [[5; 3; 7]; [2; 3; 7]; [1; 3; 7]; [5; 4; 7]; [2; 4; 7];
    /// [1; 4; 7]; [5; 3; 6]; [2; 3; 6]; [1; 3; 6]; [5; 4; 6];
    /// [2; 4; 6]; [1; 4; 6]]
    let rec cartesian = function
        | h::[] ->
            List.fold (fun acc elem -> [elem]::acc) [] h
        | h::t ->
            List.fold (fun cacc celem ->
                (List.fold (fun acc elem -> (elem::celem)::acc) [] h) @ cacc
                ) [] (cartesian t)
        | _ -> []

/// https://stackoverflow.com/questions/7818277/is-there-a-standard-option-workflow-in-f
type OptionBuilder() =
    member __.Bind(v, f) = Option.bind f v
    member __.Return(v) = Some v
    member __.ReturnFrom(o) = o
    member __.Zero() = None

[<AutoOpen>]
module OptionAutoOpen =

    /// Build for option monad.
    let opt = OptionBuilder()

module Seq =

    /// Applies a function to each item in a sequence, short-circuiting
    /// if the function fails.
    let tryFold folder state source =
        let folder' stateOpt item =
            stateOpt
                |> Option.bind (fun state ->
                    folder state item)
        Seq.fold folder' (Some state) source

module String =

    /// Concatenates the given items in a string, using the specified
    /// separator between each one.    
    let join separator (items : seq<'t>) =
        String.Join(separator, items)
