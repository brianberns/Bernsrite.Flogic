namespace Bernsrite.Flogic

/// http://intrologic.stanford.edu/extras/equality.html
module Equality =

    /// Equality predicate.
    let predicate = Predicate ("=", 2)

    /// Simple parser.
    let private parser = Parser.makeParser Array.empty

    /// Basic equality axioms.
    let basicAxioms =
        [|
            "∀x.=(x,x)"                                   // reflexive
            "∀x.∀y.(=(x,y) ⇒ =(y,x))"                   // symmetric
            "∀x.∀y.∀z.((=(x,y) ∧ =(y,z)) ⇒ =(x,z))"   // transitive
        |] |> Array.map (Parser.run parser)

    /// Tries to create a substitution axiom for the given predicate.
    let private tryGetPredicateAxiom (Predicate (name, arity)) =
        match arity with
            | 0 -> None
            | 2 -> sprintf "∀u.∀v.∀x.∀y.(((%s(u,v) ∧ =(u,x)) ∧ =(v,y)) ⇒ %s(x,y))" name name
                    |> Parser.run parser
                    |> Some
            | _ -> failwith "Not yet supported"

    /// Tries to create a substitution axiom for the given function.
    let private tryGetFunctionAxiom (Function (name, arity)) =
        match arity with
            | 0 -> None
            | 1 -> sprintf "∀x.∀y.∀z.((=(%s(x),z) ∧ =(x,y)) ⇒ =(%s(y),z))" name name
                    |> Parser.run parser
                    |> Some
            | 2 -> sprintf "∀u.∀v.∀x.∀y.∀z.(((=(%s(u,v),z) ∧ =(u,x)) ∧ =(v,y)) ⇒ =(%s(x,y),z))" name name
                    |> Parser.run parser
                    |> Some
            | _ -> failwith "Not yet supported"

    /// Basic axioms plus substitution axioms for the given language.
    let getAxioms language =
        [|
            yield! basicAxioms
            yield! language.Predicates
                |> Seq.where ((<>) predicate)
                |> Seq.choose tryGetPredicateAxiom
            yield! language.Functions
                |> Seq.choose tryGetFunctionAxiom
        |]
