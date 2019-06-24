namespace Discover

open System

type Arity = uint32
type Name = string

type Function = Function of Name * Arity
type Variable = Variable of Name

/// A term typically denotes an object that exists in the world.
/// E.g.
///    * Joe: constant (i.e. function of arity 0)
///    * Joe's father: function application
///    * someone: variable
[<StructuredFormatDisplay("{String}")>]
type Term =

    /// Atomic term: v
    | Term of Variable

    /// Function application: f(t1, t2, ...)
    | Application of Function * Term[]

    /// Display string.
    member this.String =
        match this with
            | Term (Variable name) -> name
            | Application ((Function (name, arity)), terms) ->
                assert(arity = uint32 terms.Length)
                if arity = 0u then name
                else
                    sprintf "%s(%s)" name <| String.Join(", ", terms)

    /// Display string.
    override this.ToString() =
        this.String

module Term =

    /// A constant is a function of arity 0.
    let (|Constant|_|) = function
        | Term (Variable _) -> None
        | Application ((Function (name, arity)), terms) ->
            assert(arity = uint32 terms.Length)
            if arity = 0u then
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

    let mutable private counter = 0

    /// Creates a Skolem function for the given variables.
    let createTerm variables =
        let name =
            counter <- counter + 1
            sprintf "[skolem%d]" counter
        let arity : Arity =
            variables
                |> Array.length
                |> uint32
        Application (
            Function (name, arity),
            variables |> Array.map Term)
