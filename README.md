# Bernsrite.Flogic
First-order (predicate) logic for F#

## Example
 
Consider this problem from the [Stanford Introduction to Logic course](http://intrologic.stanford.edu/public/section.php?section=section_08_06):

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
let parser = Parser.makeParser ["harry"; "ralph"]      // tell the parser that harry and ralph are named constants
let premise = Parser.run parser "∀y.(g(y) ⇒ d(y))"    // every greyhound is a dog
```

We can then use the resolution principle to prove our goal:

```F#
let goal = Parser.run parser "f(harry, ralph)"
let proofOpt = Derivation.tryProve [1..10] premises goal
```

This works by negating the goal and deriving a contradiction. In this case, `proofOpt` will hold the following steps:

|  # | Formula                           | Meaning                                      |
|---:|-----------------------------------|----------------------------------------------|
|  1 | `g(skolem1)`                      | Premise: `[skolem1](https://en.wikipedia.org/wiki/Skolem_normal_form)` is an arbitrary greyhound |
|  2 | `f(skolem1, z) or ~r(z)`          | Premise: If `z` is a rabbit, skolem1 is faster than `z` |
|  3 | `r(ralph)`                        | Premise: `ralph` is a rabbit                 |
|  4 | `~f(x, y) or f(x, z) or ~f(y, z)` | Premise: *faster-than* is transitive         |
|  5 | `~d(y) or f(x, y) or ~h(x)`       | Premise: If `x` is a horse and `y` is a dog, then `x` is faster than `y` |
|  6 | `d(y) or ~g(y)`                   | Premise: If `y` is a greyhound, then `y` is a dog |
|  7 | `h(harry)`                        | Premise: `harry` is a horse                  |
|  8 | `~f(harry, ralph)`                | Negated goal: `harry` is not faster than `ralph` |
|  9 | `~f(harry, y) or ~f(y, ralph)`    | No one slower than `harry` is faster than `ralph` (via 4 and 8) |
| 10 | `~f(harry, skolem1) or ~r(ralph)` | If `ralph` is a rabbit, then `harry` is not faster than `skolem1` (via 2 and 9) |
| 11 | `~f(harry, skolem1)`              | `harry` is not faster than `skolem1` (via 3 and 10) |
| 12 | `~d(skolem1) or ~h(harry)`        | If `skolem1` is a dog, then `harry` is not a horse (via 5 and 11) |
| 13 | `~g(skolem1) or ~h(harry)`        | If `skolem1` is a greyhound, then `harry` is not a horse (via 6 and 12) |
| 14 | `~h(harry)`                       | `harry` is not a horse (via 1 and 13)        |
| 15 | `⊥`                               | Contradiction (via 7 and 14)                 |
