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
