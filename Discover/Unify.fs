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

    /// Creates a substitution of the given term for the
    /// given variable.
    let create variable term =
        {
            Variable = variable
            Term = term
        }

    /// Applies the given substitutions in order to the
    /// given term.
    let apply term subs =
        (term, subs)
            ||> Seq.fold (fun acc sub ->
                Term.substitute
                    sub.Variable
                    sub.Term
                    acc)

    /// Tries to apply the given substitutions in order to the
    /// given literal formula.
    let rec tryApply literal subs =
        match literal with
            | Formula (predicate, terms) ->
                let terms' =
                    terms
                        |> Array.map (fun term ->
                            apply term subs)
                Formula (predicate, terms') |> Some
            | Not formula ->
                tryApply formula subs
                    |> Option.map Not
            | _ -> None

module Unfiy =

    /// Tries to unify the given terms by adding to the given
    /// substitutions.
    let rec private tryUnifyTerms term1 term2 subs =

            // apply substitions found so far
        let term1' = subs |> Substitution.apply term1
        let term2' = subs |> Substitution.apply term2

            // if terms match, we've succeeded
        if term1' = term2' then
            Some subs
        else
                // tries to add a new substitution (in reverse order)
            let add variable term =

                    // check for variable name conflict
                let occurs =
                    term
                        |> Term.getVariables
                        |> Set.contains variable

                    // create and remember the new substitution
                if occurs then None
                else
                    Substitution.create variable term
                        :: subs
                        |> Some

            match (term1', term2') with

                    // unify term with variable
                | Term variable, term -> add variable term
                | term, Term variable -> add variable term

                    // recurse on subterms
                | Application (function1, terms1),
                  Application (function2, terms2) ->
                    if function1 = function2 then
                        tryUnifyTermArrays terms1 terms2 subs
                    else None

    /// Tries to unify the given arrays of terms.
    and private tryUnifyTermArrays terms1 terms2 subs =
        (subs, Array.zip terms1 terms2)
            ||> Seq.tryFold (fun acc (term1'', term2'') ->
                tryUnifyTerms term1'' term2'' acc)

    /// Tries to unify two literal formulas.
    let rec tryUnify literal1 literal2 =
        match (literal1, literal2) with
            | Formula (predicate1, terms1), Formula (predicate2, terms2)
                when predicate1 = predicate2 ->
                    tryUnifyTermArrays terms1 terms2 List.empty
                        |> Option.map List.rev
            | Not formula1, Not formula2 ->
                tryUnify formula1 formula2
            | _ -> None
