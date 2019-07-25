namespace Bernsrite.Flogic

/// Peano arithmetic on the natural numbers.
module Peano =

    let zero = Constant.create "0"

    let successor = Function.create "s" 1

    let language =
        Language.create
            [| zero |]
            [|
                successor
                Function.create "+" 2
                // Function.create "*" 2
            |]
            [| Equality.predicate |]

    let private parse = Array.map (Language.parse language)

    /// Axioms that define the successor function in terms of equality.
    let successorAxioms =
        parse [|
            "∀x.∀y.(=(x, y) <-> =(s(x), s(y)))"
            "∀x.~=(s(x), 0)"
        |]

    /// Axioms that define addition in terms of the successor function.
    let plusAxioms =
        parse [|
            "∀x.=(+(x,0), x)"
            "∀x.∀y.=(+(x,s(y)), s(+(x,y)))"
        |]

    let axioms =
        Array.concat
            [|
                successorAxioms
                plusAxioms
            |]

    let system =
        {
            Language = language
            Axioms = axioms
        }
