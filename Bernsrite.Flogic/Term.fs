namespace Bernsrite.Flogic

open System

/// An unspecified object in the world.
[<StructuredFormatDisplay("{VariableName}"); RequireQualifiedAccess; Struct>]
type Variable =
    {
        /// Name of this variable.
        Name : string
    }

    /// Display string.
    override this.ToString() =
        this.Name

module Variable =

    /// Creates a variable with the given name.
    let create name =
        { Variable.Name = name }

    /// Answers the name of the given variable.
    let name (variable : Variable) =
        variable.Name

    /// Proposes a new name for the given variable.
    let private rename (variable : Variable) =
        create (variable.Name + "'")

    /// Renames the given variable if necessary to avoid conflict
    /// with the given variables.
    let rec deconflictSet variables variable =
        if variables |> Set.contains(variable) then
            variable
                |> rename
                |> deconflictSet variables
        else
            let variables' = variables |> Set.add variable
            variable, variables'

    /// Renames the given variable if necessary to avoid conflict
    /// with the given variables.
    let deconflictMap variableMap variable =

        let rec deconflict (variable : Variable) =
            let variable' = rename variable
            if variableMap |> Map.containsKey(variable') then
                variable' |> deconflict
            else
                variable'

        let variable', isAdd =
            match variableMap |> Map.tryFind variable with

                    // variable has been previously renamed
                | Some (Some variable') ->
                    variable', false

                    // conflict, must rename
                | Some None ->
                    deconflict variable, true

                    // no conflict
                | None ->
                    variable, true

        let variableMap' =
            if isAdd then
                variableMap
                    |> Map.add variable (Some variable')
                    |> Map.add variable' None
            else
                variableMap

        variable', variableMap'

/// A specific object in the world.
[<StructuredFormatDisplay("{ConstantName}"); RequireQualifiedAccess; Struct>]
type Constant =
    {
        /// Name of this constant.
        Name : string
    }

    /// Display string.
    override this.ToString() =
        this.Name

module Constant =

    /// Creates a constant with the given name.
    let create name =
        { Constant.Name = name }

    /// Answers the name of the given constant.
    let name (constant : Constant) =
        constant.Name

/// A function that takes some number of arguments.
[<RequireQualifiedAccess; Struct>]
type Function =
    {
        /// Name of this function.
        Name : string

        /// Number of arguments.
        Arity : int
    }

module Function =

    /// Creates a function with the given name and arity.
    let create name arity =
        {
            Function.Name = name
            Function.Arity = arity
        }

/// A term typically denotes an object that exists in the world.
/// E.g.
///    * someone: variable
///    * Joe: constant
///    * Joe's father: function application (i.e. father(joe))
[<StructuredFormatDisplay("{String}")>]
type Term =

    /// An atomic variable term.
    | VariableTerm of Variable

    /// An atomic constant term.
    | ConstantTerm of Constant

    /// Function application: f(t1, t2, ...)
    | Application of Function * Term[]

    /// Display string.
    member this.String =
        match this with
            | VariableTerm variable -> variable.Name
            | ConstantTerm constant -> constant.Name
            | Application (func, terms) ->
                if (func.Arity <> terms.Length) then
                    failwith "Arity mismatch"
                sprintf "%s(%s)" func.Name <| String.Join(",", terms)

    /// Display string.
    override this.ToString() =
        this.String

module Term =

    /// Answers the distinct variables contained in the given term.
    let getVariables term =

        let rec loop term =
            seq {
                match term with
                    | VariableTerm var -> yield var
                    | ConstantTerm _ -> ()
                    | Application (_, terms) ->
                        for term in terms do
                            yield! term |> loop
            }

        term
            |> loop
            |> set

    /// Answers the number of symbols in the given term.
    let rec symbolCount = function
        | VariableTerm _
        | ConstantTerm _ -> 1
        | Application (_, terms) ->
            let termCount =
                terms
                    |> Seq.sumBy symbolCount
            termCount + 1   // +1 for function

    /// Substitutes the given new term for the given variable in the given
    /// old term.
    let rec substitute variable newTerm oldTerm =
        match oldTerm with
            | VariableTerm var ->
                if var = variable then newTerm
                else oldTerm
            | ConstantTerm _ -> oldTerm
            | Application (func, oldTerms) ->
                Application (
                    func,
                    oldTerms
                        |> substituteTerms variable newTerm)

    /// Substitutes the given new term for the given variable in the given
    /// old terms.
    and substituteTerms variable newTerm oldTerms =
        oldTerms |> Array.map (substitute variable newTerm)

/// http://intrologic.stanford.edu/public/section.php?section=section_08_03
module Skolem =

    /// Number of Skolem functions created so far.
    let mutable private counter = 0

    /// Creates a Skolem constant or function for the given terms.
    let create (terms : _[]) =
        let name =
            counter <- counter + 1
            sprintf "skolem%d" counter
        if terms.Length = 0 then
            ConstantTerm (Constant.create name)
        else
            Application (
                Function.create name terms.Length,
                terms)
