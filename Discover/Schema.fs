namespace Discover

/// Placeholder for a predicate.
type MetaVariable = Formula

module MetaVariable =

    /// Creates a metavariable. This is currently implemented as
    /// 0-arity placeholder for a predicate.
    let create name : MetaVariable =
        Formula (
            Predicate (name, arity = 0),
            Array.empty)

/// A schema is a formula that might contain metavariables.
type Schema = Formula

/// Mapping of metavariables to formulas.
type Binding = Map<MetaVariable, Formula>

module Schema =

    /// Active pattern for a metavariable.
    let (|MetaVariable|_|) = function
        | Formula ((Predicate (name, arity)), terms)
            when arity = 0 ->
                if (terms.Length > 0) then
                    failwith "Arity mismatch"
                Some name
        | _ -> None

    /// Finds possible mappings for the given formula using the given
    /// schema (including potentially contradictory ones).
    let private findMappingOpts formula schema =

        let rec loop formula (schema : Schema) =
            seq {
                match (formula, schema) with

                        // bind metavariable
                    | _, MetaVariable _ ->
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

    /// Applies the given binding to the given schema.
    let rec apply (binding : Binding) (schema : Schema) =
        match schema with

                // bind with metavariable
            | MetaVariable name as metaVariable ->
                match binding |> Map.tryFind metaVariable with
                    | Some formula -> formula
                    | None -> failwithf "No binding for metavariable %s" name

                // recurse
            | Not schema' ->
                Not (
                    schema' |> apply binding)
            | And (schema1, schema2) ->
                And (
                    schema1 |> apply binding,
                    schema2 |> apply binding)
            | Or (schema1, schema2) ->
                Or (
                    schema1 |> apply binding,
                    schema2 |> apply binding)
            | Implication (schema1, schema2) ->
                Implication (
                    schema1 |> apply binding,
                    schema2 |> apply binding)
            | Biconditional (schema1, schema2) ->
                Biconditional (
                    schema1 |> apply binding,
                    schema2 |> apply binding)

                // error
            | _ -> failwith "Unexpected"
