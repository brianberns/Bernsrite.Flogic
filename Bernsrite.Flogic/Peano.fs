namespace Bernsrite.Flogic

module Peano =

    let zero = Constant "0"

    let successor = Function ("s", 1)

    let language =
        Language.create
            [| zero |]
            [|
                successor
                Function ("+", 2)
                // Function ("*", 2)
            |]
            [| Equality.predicate |]

    let private parse = Array.map (Language.parse language)

    let plusAxioms =
        parse [|
            "∀x.=(+(x,0), x)"
            "∀x.∀y.=(+(x,s(y)), s(+(x,y)))"
        |]

    let axioms =
        [|
            yield! plusAxioms
        |]

    let system =
        {
            Language = language
            Axioms = axioms
        }
