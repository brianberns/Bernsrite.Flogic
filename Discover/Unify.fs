namespace Discover

/// Substitution of the given variables with the given terms.
[<StructuredFormatDisplay("{String}")>]
type Substitution =
    {
        SubstMap : Map<Variable, Term>
    }

    /// Display string.
    member this.String =
        this.SubstMap
            |> Map.toSeq
            |> Seq.sort
            |> Seq.map (fun (variable, term) ->
                sprintf "%A <- %A" variable term)
            |> String.join ", "

    /// Display string.
    override this.ToString() =
        this.String

module Substitution =

    /// The empty substitution.
    let empty =
        {
            SubstMap = Map.empty
        }

    /// Creates a substitution containing only the given mapping.
    let create variable term =
        {
            SubstMap = Map [ variable, term ]
        }

    /// Applies the given substitution to the given term.
    let rec applyTerm subst = function
        | Term var as term ->
            subst.SubstMap
                |> Map.tryFind var
                |> Option.defaultValue term
        | Application (func, terms) ->
            Application (
                func,
                terms
                    |> Array.map (applyTerm subst))

    /// Applies the given substitution to the given literal.
    let rec applyLiteral subst literal =

        let applyTerms predicate terms constructor =
            let terms' =
                terms |> Array.map (applyTerm subst)
            Formula (predicate, terms')
                |> constructor
                |> Literal.ofFormula

        match literal with
            | LiteralAtom (predicate, terms) ->
                applyTerms predicate terms id
            | LiteralNot (predicate, terms) ->
                applyTerms predicate terms Not

    let getDomainVariables subst =
        subst.SubstMap
            |> Map.toSeq
            |> Seq.map fst
            |> set

    let getRangeVariables subst =
        subst.SubstMap
            |> Map.toSeq
            |> Seq.collect (snd >> Term.getVariables)
            |> set

    /// Indicates whether the given subtitution is pure.
    let isPure subst =
        Set.intersect
            (getDomainVariables subst)
            (getRangeVariables subst)
            |> Set.isEmpty

    /// Indicates whether the given substitutions are composable.
    let composable subst1 subst2 =
        Set.intersect
            (getDomainVariables subst1)
            (getRangeVariables subst2)
            |> Set.isEmpty

    /// Creates a new substitution with the same effect as applying
    /// the two given substitutions in order: subst1 >> subst2
    let compose subst1 subst2 =
        assert(isPure subst1)
        assert(isPure subst2)
        assert(composable subst1 subst2)
        {
            SubstMap =
                seq {
                    for (KeyValue(variable1, term1)) in subst1.SubstMap do
                        yield variable1, (term1 |> applyTerm subst2)
                    for (KeyValue(variable2, term2)) in subst2.SubstMap do
                        if subst1.SubstMap.ContainsKey(variable2) |> not then
                            yield variable2, term2
                } |> Map.ofSeq
        }

module Unfiy =

    /// Tries to unify the given terms by adding to the given
    /// substitution.
    let rec private tryUnifyTerms term1 term2 subst =

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
                    let subst' =
                        Substitution.compose
                            subst
                            (Substitution.create variable term)
                    subst'
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
    and private tryUnifyTermArrays terms1 terms2 subst =
        (subst, Array.zip terms1 terms2)
            ||> Seq.tryFold (fun acc (term1'', term2'') ->
                tryUnifyTerms term1'' term2'' acc)

    /// Tries to unify two literals.
    let tryUnify literal1 literal2 =

        match (literal1, literal2) with
            | LiteralAtom (predicate1, terms1),
              LiteralAtom (predicate2, terms2)
                when predicate1 = predicate2 ->
                    tryUnifyTermArrays terms1 terms2 Substitution.empty
            | LiteralNot (predicate1, terms1),
              LiteralNot (predicate2, terms2)
                when predicate1 = predicate2 ->
                    tryUnifyTermArrays terms1 terms2 Substitution.empty
            | _ -> None
