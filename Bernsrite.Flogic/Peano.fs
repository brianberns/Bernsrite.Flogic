namespace Bernsrite.Flogic

/// Peano arithmetic on the natural numbers.
module Peano =

    /// Zero constant.
    let zero = Constant.create "0"

    /// Successor function.
    let successor = Function.create "s" 1

    /// Peano language. E.g. ∀x.(x + s(0) = s(x)).
    let language =
        Language.create
            [| zero |]
            [|
                successor
                Function.create "+" 2
                // Function.create "*" 2
            |]
            [| Equality.predicate |]

    /// Peano parser.
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

    /// Explicit Peano axioms.
    let axioms =
        Array.concat
            [|
                successorAxioms
                plusAxioms
            |]

    /// Peano arithmetic.
    let theory =
        {
            Language = language
            Axioms = axioms
        }
