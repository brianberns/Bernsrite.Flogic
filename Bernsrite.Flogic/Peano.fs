namespace Bernsrite.Flogic

/// http://intrologic.stanford.edu/public/section.php?section=section_09_04
module Peano =

    let parser =
        Parser.makeParser ["0"]

    let parse = Array.map (Parser.run parser)

    let equalsAxioms =
        parse [|
            "∀x.=(x,x)"
            "∀x.(¬=(0,s(x)) ∧ ¬=(s(x),0))"
            "∀x.∀y.(¬=(x,y) ⇒ ¬=(s(x),s(y)))"
        |]

    let plusAxioms =
        parse [|
            "∀y.+(0,y,y)"
            "∀x.∀y.∀z.(+(x,y,z) ⇒ +(s(x),y,s(z)))"
            "∀x.∀y.∀z.∀w.((+(x,y,z) ∧ ¬=(z,w)) ⇒ ¬+(x,y,w))"
        |]

    let timesAxioms =
        parse [|
            "∀y.*(0,y,0)"
            "∀x.∀y.∀z.∀w.((*(x,y,z) ∧ +(y,z,w)) ⇒ *(s(x),y,w))"
            "∀x.∀y.∀z.∀w.((*(x,y,z) ∧ ¬=(z,w)) ⇒ ¬*(x,y,w))"
        |]

    let axioms =
        [|
            yield! equalsAxioms
            yield! plusAxioms
            yield! timesAxioms
        |]
