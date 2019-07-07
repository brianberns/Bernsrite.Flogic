# Bernsrite.Flogic
First-order (predicate) logic for F#

## Overview
 
As an example, consider this problem from the [Stanford Introduction to Logic course](http://intrologic.stanford.edu/public/):

> We know that horses are faster than dogs and that there is a greyhound that is faster than every rabbit. We know that Harry is a horse and that Ralph is a rabbit. Our job is to derive the fact that Harry is faster than Ralph.

We write the premises (including implicit ones) in first-order logic as follows:

| Formula                                  | Meaning                                             |
| -----------------------------------------|-----------------------------------------------------|
| ∀x.∀y.(h(x) ∧ d(y) ⇒ f(x,y))         | Every horse is faster than every dog                |
| ∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y,z)))       | There's a greyhound that's faster than every rabbit |
| ∀y.(g(y) ⇒ d(y))                       | Every greyhound is a dog                            |
| ∀x.∀y.∀z.(f(x,y) ∧ f(y,z) ⇒ f(x,z)) | The *faster than* relationship is transitive        |
| h(harry)                                 | Harry is a horse                                    |
| r(ralph)                                 | Ralph is a rabbit                                   |

We can code this directly into F# using the Flogic [DSL](https://en.wikipedia.org/wiki/Domain-specific_language). For example, this says every greyhound is a dog:

```F#
ForAll (
    Variable "y",
    Implication (
        Formula (
            Predicate ("greyhound", 1),
            [| Term (Variable "y") |]),
        Formula (
            Predicate ("dog", 1),
            [| Term (Variable "y") |])))
```

However, rather than write out each premise the long way, we can use a parser instead:

```F#
let parser = Parser.makeParser ["harry"; "ralph"]     // tell the parser that harry and ralph are named constants
let formula = Parser.run parser "∀y.(g(y) ⇒ d(y))"   // every greyhound is a dog
```
