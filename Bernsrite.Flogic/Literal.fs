namespace Bernsrite.Flogic

open System

/// A literal is either an atomic formula or its negation.
[<StructuredFormatDisplay("{String}")>]
type Literal =
    {
        Predicate : Predicate
        Terms : Term[]
        IsPositive : bool
    }

    /// Display string.
    member this.String =
        let (Predicate (name, arity)) = this.Predicate
        if (arity <> this.Terms.Length) then
            failwith "Arity mismatch"
        if arity = 0 then name
        elif Char.IsSymbol(name.[0]) && arity = 3 then
            sprintf "%A %s %A %s %A"
                this.Terms.[0]
                name
                this.Terms.[1]
                (if this.IsPositive then "=" else "<>")
                this.Terms.[2]
        else
            sprintf "%s%s(%s)"
                (if this.IsPositive then "" else "~")
                name
                (String.Join(", ", this.Terms))

    /// Display string.
    override this.ToString() =
        this.String

module Literal =

    /// Display string.
    let toString (literal : Literal) =
        literal.ToString()

    /// Creates a literal.
    let private create predicate terms isPositive =
        {
            Predicate = predicate
            Terms = terms
            IsPositive = isPositive
        }

    /// Converts a formula to a literal.
    let ofFormula = function
        | Formula (predicate, terms) ->
            create predicate terms true
        | Not (Formula (predicate, terms)) ->
            create predicate terms false
        | _ -> failwith "Not a literal"

    /// Negates the given literal.
    let negate literal =
        {
            literal with
                IsPositive = not literal.IsPositive
        }

    /// Applies the given mapping to the given literal's terms.
    let map mapping literal =
        {
            literal with
                Terms = literal.Terms |> Array.map mapping
        }

    /// Tries to unify two literals.
    let tryUnify literal1 literal2 =

        /// Tries to unify the given terms by adding to the given
        /// substitution.
        let rec tryUnifyTerms term1 term2 subst =

                // apply substitions found so far
            let term1' = term1 |> Substitution.applyTerm subst
            let term2' = term2 |> Substitution.applyTerm subst

                // if terms match, we've succeeded
            if term1' = term2' then
                Some subst
            else
                    // tries to add to the substitution
                let add variable term =

                        // check for variable name conflict
                    let occurs =
                        term
                            |> Term.getVariables
                            |> Set.contains variable
                    if occurs then None
                    else
                            // update the substitution
                        Substitution.compose
                            subst
                            (Substitution.create variable term)
                            |> Some

                match (term1', term2') with

                        // unify term with variable
                    | Term variable, term -> add variable term
                    | term, Term variable -> add variable term

                        // recurse on subterms
                    | Application (function1, terms1),
                      Application (function2, terms2) ->
                        if function1 = function2 then
                            tryUnifyTermArrays terms1 terms2 subst
                        else None

        /// Tries to unify the given arrays of terms.
        and tryUnifyTermArrays terms1 terms2 subst =
            (subst, Array.zip terms1 terms2)
                ||> Seq.tryFold (fun acc (term1'', term2'') ->
                    tryUnifyTerms term1'' term2'' acc)

        if literal1.IsPositive = literal2.IsPositive
            && literal1.Predicate = literal2.Predicate then
            tryUnifyTermArrays literal1.Terms literal2.Terms Substitution.empty
        else None
