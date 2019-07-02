namespace Discover

open System

/// A function that takes some number of arguments.
type Function = Function of name : string * arity : int

/// A variable that represents an object in the world.
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

/// A term typically denotes an object that exists in the world.
/// E.g.
///    * Joe: constant
///    * Joe's father: function application (i.e. father(joe))
///    * someone: variable
[<StructuredFormatDisplay("{String}")>]
type Term =

    /// An atomic term.
    | Term of Variable

    /// Function application: f(t1, t2, ...)
    | Application of Function * Term[]

    /// Display string.
    member this.String =
        match this with
            | Term variable -> variable.Name
            | Application (Function (name, arity), terms) ->
                if (arity <> terms.Length) then
                    failwith "Arity mismatch"
                if arity = 0 then name
                else
                    sprintf "%s(%s)" name <| String.Join(",", terms)

    /// Display string.
    override this.ToString() =
        this.String

module Term =

    /// Creates a constant term with the given name. A constant is a
    /// function of arity 0.
    let constant name =
        Application (
            (Function (name, arity = 0)),
            Array.empty)

    /// Answers the distinct variables contained in the given term.
    let getVariables term =

        let rec loop term =
            seq {
                match term with
                    | Term var -> yield var
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
            | Term var ->
                if var = variable then newTerm
                else oldTerm
            | Application (func, oldTerms) ->
                Application (
                    func,
                    oldTerms |> substituteTerms variable newTerm)

    /// Substitutes the given new term for the given variable in the given
    /// old terms.
    and substituteTerms variable newTerm oldTerms =
        oldTerms |> Array.map (substitute variable newTerm)

/// http://intrologic.stanford.edu/public/section.php?section=section_08_03
module Skolem =

    /// Number of Skolem functions created so far.
    let mutable private counter = 0

    /// Creates a Skolem function for the given terms.
    let create terms =
        let name =
            counter <- counter + 1
            sprintf "skolem%d" counter
        let func =
            Function (name, terms |> Array.length)
        let term =
            Application (func, terms)
        func, term
