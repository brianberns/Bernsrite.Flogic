namespace Discover

open System

/// A function that takes some number of arguments.
type Function = Function of name : string * arity : int

/// A variable that represents an object in the world.
type Variable = Variable of name : string

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
            | Term (Variable name) -> name
            | Application (Function (name, arity), terms) ->
                assert(arity = terms.Length)
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

    /// Active pattern for a constant term.
    let (|Constant|_|) = function
        | Term (Variable _) -> None
        | Application ((Function (name, arity)), terms) ->
            assert(arity = terms.Length)
            if arity = 0 then
                Some name
            else None

    /// Indicates whether the given term is "ground" (i.e. contains no
    /// variables).
    let rec isGround = function
        | Term (Variable _) -> false
        | Constant _ -> true
        | Application (Function _, terms) ->
            terms |> Seq.forall isGround

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

/// http://intrologic.stanford.edu/public/section.php?section=section_08_03
module Skolem =

    /// Number of Skolem functions created so far.
    let mutable private counter = 0

    /// Creates a Skolem function of the given arity.
    let createFunction arity =
        let name =
            counter <- counter + 1
            sprintf "[skolem%d]" counter
        Function (name, arity)
