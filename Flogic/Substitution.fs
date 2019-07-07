namespace Flogic

/// Substitution of terms for variables.
[<StructuredFormatDisplay("{String}")>]
type Substitution =
    {
        SubstMap : (string (*variable name*) * Term)[]
    }

    /// Display string.
    member this.String =
        this.SubstMap
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
            SubstMap = Array.empty
        }

    /// Creates a substitution containing only the given mapping.
    let create (Variable name) term =
        {
            SubstMap = [| name, term |]
        }

    /// Applies the given substitution to the given term.
    let rec applyTerm subst term =
        if subst.SubstMap.Length = 0 then
            term
        else
            match term with
                | Term (Variable name) as term ->
                    subst.SubstMap
                        |> Array.tryPick (fun (name', term') ->
                            if name' = name then Some term'
                            else None)
                        |> Option.defaultValue term
                | Application (func, terms) ->
                    Application (
                        func,
                        terms
                            |> Array.map (applyTerm subst))

    /// Answers names of variables in the domain of the given substitution.
    let getDomainVariableNames subst =
        subst.SubstMap
            |> Seq.map fst
            |> set

    /// Answers names of variables in the range of the given substitution.
    let getRangeVariableNames subst =
        subst.SubstMap
            |> Seq.collect (
                snd
                    >> Term.getVariables
                    >> Seq.map (fun (Variable name) -> name))
            |> set

    /// Indicates whether the given subtitution is pure.
    let isPure subst =
        Set.intersect
            (getDomainVariableNames subst)
            (getRangeVariableNames subst)
            |> Set.isEmpty

    /// Indicates whether the given substitutions are composable.
    let composable subst1 subst2 =
        Set.intersect
            (getDomainVariableNames subst1)
            (getRangeVariableNames subst2)
            |> Set.isEmpty

    /// Creates a new substitution with the same effect as applying
    /// the two given substitutions in order: subst1 >> subst2
    let compose subst1 subst2 =
        assert(isPure subst1)
        assert(isPure subst2)
        assert(composable subst1 subst2)
        {
            SubstMap =
                [|
                    for (name1, term1) in subst1.SubstMap do
                        yield name1, (term1 |> applyTerm subst2)
                    for (name2, term2) in subst2.SubstMap do
                        let exists =
                            subst1.SubstMap
                                |> Array.exists (fun (name, _) ->
                                    name = name2)
                        if not exists then
                            yield name2, term2
                |]
        }
