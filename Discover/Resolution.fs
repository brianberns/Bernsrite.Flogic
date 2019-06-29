namespace Discover

/// Substitute the given term for the given variable.
[<StructuredFormatDisplay("{String}")>]
type Substitution =
    {
        /// Variable being replaced.
        Variable : Variable

        /// Term that is replacing the variable.
        Term : Term
    }

    /// Display string.
    member this.String =
        sprintf "%A <- %A" this.Variable this.Term

    /// Display string.
    override this.ToString() =
        this.String

module Substitution =

    let apply term subs =
        (term, subs)
            ||> Seq.fold (fun acc sub ->
                Term.substitute
                    sub.Variable
                    sub.Term
                    acc)

    let add variable term subs =
        subs
            |> Set.add {
                Variable = variable
                Term = term
            }

module Resolution =

    let rec private unifyTerms term1 term2 subs =

        let add variable term =
            let occurs =
                term
                    |> Term.getVariables
                    |> Set.contains variable
            if occurs then None
            else
                subs
                    |> Substitution.add variable term
                    |> Some

        let term1' = subs |> Substitution.apply term1
        let term2' = subs |> Substitution.apply term2
        if term1' = term2' then
            Some subs
        else
            match (term1', term2') with

                    // unify term with variable
                | Term variable, term -> add variable term
                | term, Term variable -> add variable term

                    // recurse
                | Application (function1, terms1),
                    Application (function2, terms2) ->
                    if function1 = function2 then
                        unifyTermArrays terms1 terms2 subs
                    else None

    and private unifyTermArrays terms1 terms2 subs =
        (subs, Array.zip terms1 terms2)
            ||> Seq.tryFold (fun acc (term1'', term2'') ->
                unifyTerms term1'' term2'' acc)

    let unify formula1 formula2 =

        let toAtom = function
            | Formula (_, _) as formula -> formula
            | Not (Formula (_, _) as formula) -> formula
            | _ -> failwith "Not a literal"

        match (toAtom formula1, toAtom formula2) with
            | Formula (predicate1, terms1), Formula (predicate2, terms2)
                when predicate1 = predicate2 ->
                    unifyTermArrays terms1 terms2 Set.empty
            | _ -> None
