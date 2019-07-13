namespace Bernsrite.Flogic

/// https://en.wikipedia.org/wiki/Robinson_arithmetic
module Robinson =

    let language =
        Language.create
            [| Constant "0" |]
            [|
                Function ("s", 1)
                Function ("+", 2)
                Function ("*", 2)
            |]
            [| Predicate ("=", 2) |]

    let private parse = Array.map (Language.parse language)

    let equalsAxioms =
        parse [|
            "∀x.~=(s(x), 0)"
            "∀x.∀y.(=(s(x), s(y)) -> =(x, y))"
            "∀y.(=(y, 0) | ∃x.=(s(x), y))"
        |]

    let plusAxioms =
        parse [|
            "∀x.=(+(x,0), x)"
            "∀x.∀y.=(+(x,s(y)), s(+(x,y)))"
        |]

    let timesAxioms =
        parse [|
            "∀x.=(*(x,0), 0)"
            "∀x.∀y.=(*(x,s(y)), +(*(x,y),x))"
        |]

    let axioms =
        [|
            yield! equalsAxioms
            yield! plusAxioms
            // yield! timesAxioms
        |]
