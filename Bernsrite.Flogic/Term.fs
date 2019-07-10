namespace Bernsrite.Flogic

open System

/// An unspecified object in the world.
[<StructuredFormatDisplay("{Name}")>]
type Variable =
    | Variable of name : string

    /// Variable's name.
    member this.Name =
        let (Variable name) = this
        name

    /// Display string.
    override this.ToString() =
        this.Name

module Variable =

    /// Renames the given variable if necessary to avoid conflict
    /// with the given variables.
    let rec deconflict seen ((Variable name) as variable) =
        if seen |> Set.contains(variable) then
            Variable (name + "'") |> deconflict seen
        else
            let seen' = seen |> Set.add variable
            variable, seen'

/// A specific object in the world.
[<StructuredFormatDisplay("{Name}")>]
type Constant =
    | Constant of name : string

    /// Constant's name.
    member this.Name =
        let (Constant name) = this
        name

    /// Display string.
    override this.ToString() =
        this.Name

/// A function that takes some number of arguments.
type Function = Function of name : string * arity : int

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
            | Application (Function (name, arity), terms) ->
                if (arity <> terms.Length) then
                    failwith "Arity mismatch"
                sprintf "%s(%s)" name <| String.Join(",", terms)

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
            ConstantTerm (Constant name)
        else
            Application (
                Function (name, terms.Length),
                terms)
