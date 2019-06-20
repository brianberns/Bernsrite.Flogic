namespace Discover

type MetaVariable = Formula

module MetaVariable =

    /// Creates a metavariable. This is currently implemented as
    /// 0-arity placeholder for a predicate.
    let create name : MetaVariable =
        Holds (Predicate (name, 0u), [])

    let nameOf (metaVar : MetaVariable) =
        match metaVar with
            | Holds (Predicate (name, 0u), []) -> name
            | _ -> failwith "Unexpected"

/// A schema is a formula that might contain metavariables.
type Schema = Formula

/// Binding of metavariables to formulas.
type Binding = Map<MetaVariable, Formula>

module Schema =

    /// Finds possible mappings of the given formula to the given
    /// schema (including potentially contradictory ones).
    let private findMappingOpts formula schema =

        let rec loop formula (schema : Schema) =
            seq {
                match (formula, schema) with

                        // bind metavariable
                    | _, Holds (Predicate (_, 0u), terms) ->
                        assert(terms.Length = 0)
                        yield Some ((schema : MetaVariable), formula)

                        // recurse
                    | Not formula', Not schema' ->
                        yield! schema' |> loop formula'
                    | And (formula1, formula2), And (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Or (formula1, formula2), Or (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Implication (formula1, formula2), Implication (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2
                    | Biconditional (formula1, formula2), Biconditional (schema1, schema2) ->
                        yield! schema1 |> loop formula1
                        yield! schema2 |> loop formula2

                        // error
                    | _ -> yield None
            }

        schema
            |> loop formula
            |> Seq.toArray

    /// Resolves errors or incompatibilities in the given mappings.
    let private resolve mappingOpts : Option<Binding> =

            // did an error occur?
        let mappings =
            mappingOpts |> Array.choose id
        assert(mappings.Length <= mappingOpts.Length)
        if mappings.Length = mappingOpts.Length then

                // validate mappings
            let distinct = mappings |> Array.distinct
            let isValid =
                distinct
                    |> Seq.groupBy fst
                    |> Seq.forall (fun (_, group) ->
                        (group |> Seq.length) = 1)

                // package mappings into a binding
            if isValid then
                let binding = distinct |> Map.ofSeq
                assert(binding.Count = distinct.Length)
                Some binding
            else None

        else None

    /// Finds all possible bindings of the given formulas to the
    /// given schemas.
    let bind formulas schemas =
        if Array.length formulas >= Array.length schemas then
            formulas
                |> List.ofArray
                |> List.permutations schemas.Length
                |> Seq.choose (fun formulaList ->
                    Seq.zip formulaList schemas
                        |> Seq.collect (fun (formula, schema) ->
                            schema |> findMappingOpts formula)
                        |> Seq.toArray
                        |> resolve)
                |> Seq.toArray
        else Array.empty

    /// Substitutes the given bindings in the given schema.
    let rec substitute bindings (schema : Schema) =
        match schema with

                // bind with placeholder
            | Holds (Predicate (name, 0u), terms) ->
                assert(terms.Length = 0)
                match bindings |> Map.tryFind schema with
                    | Some formula -> formula
                    | None -> failwithf "No binding for metavariable %s" name

                // recurse
            | Not formula ->
                Not (
                    formula |> substitute bindings)
            | And (formula1, formula2) ->
                And (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Or (formula1, formula2) ->
                Or (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Implication (formula1, formula2) ->
                Implication (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)
            | Biconditional (formula1, formula2) ->
                Biconditional (
                    formula1 |> substitute bindings,
                    formula2 |> substitute bindings)

                // error
            | _ -> failwith "Unexpected"
