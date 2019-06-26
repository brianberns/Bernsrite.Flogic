﻿namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1)
    let isMortal = Predicate ("Mortal", 1)
    let x = [| Term (Variable "x") |]

    [<TestMethod>]
    member __.ImplicationElimination() =
        let conclusions =
            InferenceRule.implicationElimination
                |> InferenceRule.apply
                    [|
                        Implication (
                            Formula (isMan, x),
                            Formula (isMortal, x))
                        Formula (isMan, x)
                    |]
        Assert.AreEqual(1, conclusions.Length)
        Assert.AreEqual(1, conclusions.[0].Length)
        Assert.AreEqual(Formula (isMortal, x), conclusions.[0].[0])

    [<TestMethod>]
    member __.ImplicationCreation() =
        let implicationCreation =
            let p = MetaVariable.create "P"
            let q = MetaVariable.create "Q"
            {
                Premises = [| q |]
                Conclusions = [| Implication (p, q) |]
                Name = "implicationCreation"
            }
        let premises =
            [|
                Formula (isMan, x)
                Formula (isMortal, x)
            |]
        let bindings =
            implicationCreation.Premises
                |> Schema.bind premises
        Assert.AreEqual(premises.Length, bindings.Length)

    member __.TryProve(steps) =
        (Ok Proof.empty, steps)
            ||> Seq.fold (fun proofResult (formulas, rule, indexes) ->
                match proofResult with
                    | Ok proof ->
                        match proof |> Proof.tryAddSteps formulas rule indexes with
                            | Some proof' -> Ok proof'
                            | None -> Error (proof.Steps.Length + 1)
                    | _ -> proofResult)

    member this.Prove(steps) =
        match this.TryProve(steps) with
            | Ok proof ->
                printfn "%A" proof
                Assert.IsTrue(proof |> Proof.isComplete)
            | Error index -> Assert.Fail(sprintf "Step %d" index)

    /// http://intrologic.stanford.edu/public/section.php?section=section_04_03
    [<TestMethod>]
    member this.PropositionalProof1() =

        let p = MetaVariable.create "p"
        let q = MetaVariable.create "q"
        let r = MetaVariable.create "r"

        let steps =
            [|
                [
                    (*1*) Implication (p, q)
                    (*2*) Implication (q, r)
                ], InferenceRule.Premise, Array.empty;
                (*3*) [ p ], InferenceRule.Assumption, Array.empty;
                (*4*) [ q ], InferenceRule.implicationElimination, [| 3; 1 |];
                (*5*) [ r ], InferenceRule.implicationElimination, [| 4; 2 |];
                (*6*) [ Implication (p, r) ], InferenceRule.ImplicationIntroduction, [| 3; 5 |]
            |]
        this.Prove(steps)

        let proofResult =
            [|
                yield! steps
                yield (*7*) [ MetaVariable.create "r" ], InferenceRule.implicationElimination, [| 2; 4 |]
            |] |> this.TryProve
        Assert.AreEqual(Result<Proof, _>.Error 7, proofResult)

    [<TestMethod>]
    member this.PropositionalProof2() =

        let p = MetaVariable.create "p"
        let q = MetaVariable.create "q"
        let reiteration =
            Ordinary {
                Premises = [| p |]
                Conclusions = [| p |]
                Name = "Reiteration"
            }

        [|
            [
                (*1*) Or (p, q)
                (*2*) Not p
            ], Premise, Array.empty;
            (*3*) [ p ], Assumption, Array.empty;
            (*4*) [ Not q ], Assumption, Array.empty;
            (*5*) [ p ], reiteration, [| 3 |];
            (*6*) [ Implication (Not q, p) ], ImplicationIntroduction, [| 4; 5 |];
            (*7*) [ Not q ], Assumption, Array.empty;
            (*8*) [ Not p ], reiteration, [| 2 |];
            (*9*) [ Implication (Not q, Not p) ], ImplicationIntroduction, [| 7; 8 |];
            (*10*) [ Not (Not q) ], InferenceRule.notIntroduction, [| 6; 9 |];
            (*11*) [ q ], InferenceRule.notElimination, [| 10 |];
            (*12*) [ Implication (p, q) ], ImplicationIntroduction, [| 3; 11 |];
            (*13*) [ q ], Assumption, Array.empty;
            (*14*) [ Implication (q, q) ], ImplicationIntroduction, [| 13 |];
            (*15*) [ q ], InferenceRule.orElimination, [| 1; 12; 14 |]
        |] |> this.Prove

    [<TestMethod>]
    member this.UniversalIntroduction() =

        let x = Variable "x"
        let p = Formula (Predicate ("p", 1), [| Term x |])
        let q = Formula (Predicate ("q", 1), [| Term x |])

        let steps =
            [|
                (*1*) [| Implication (p, q) |], InferenceRule.Premise, Array.empty
                (*2*) [| p |], InferenceRule.Assumption, Array.empty
                (*3*) [| q |], InferenceRule.implicationElimination, [| 1; 2 |]
            |]

        let proofResult =
            [|
                yield! steps
                yield (*4*) [| ForAll (x, q) |], InferenceRule.UniversalIntroduction x, [| 3 |]
            |] |> this.TryProve
        Assert.AreEqual(Result<Proof, _>.Error 4, proofResult)

        [|
            yield! steps
            yield (*4*) [| Implication (p, q) |], InferenceRule.ImplicationIntroduction, [| 2; 3 |]
            yield (*5*) [| ForAll (x, Implication (p, q)) |], InferenceRule.UniversalIntroduction x, [| 4 |]
        |] |> this.Prove

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_02
    [<TestMethod>]
    member __.UniversalElimination() =

            // "everybody hates somebody"
        let formula =
            let x = Variable "x"
            let y = Variable "y"
            ForAll (
                x,
                Exists (
                    y,
                    Formula (
                        Predicate ("hates", 2),
                        [| Term x; Term y |])))
        Assert.AreEqual(
            "∀x.∃y.hates(x, y)", formula.ToString())

            // "Jane hates somebody": valid
        let conclusions =
            UniversalElimination (Term (Variable "jane"))
                |> InferenceRule.apply [| formula |]
        Assert.AreEqual(1, conclusions.Length)
        Assert.AreEqual(1, conclusions.[0].Length)
        Assert.AreEqual(
            "∃y.hates(jane, y)",
            conclusions.[0].[0].ToString())

            // "somebody hates herself": ∃y.hates(y, y), invalid
        let conclusions =
            UniversalElimination (Term (Variable "y"))
                |> InferenceRule.apply [| formula |]
        Assert.AreEqual(0, conclusions.Length)

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_05
    [<TestMethod>]
    member this.QuantifiedProof1() =

        let x = Variable "x"
        let y = Variable "y"
        let z = Variable "z"
        let loves = Predicate ("loves", 2)

        [|
            (*1*)
            [|
                ForAll (
                    y,
                    Exists (
                        z,
                        Formula (loves, [| Term y; Term z |])))
            |],
            InferenceRule.Premise,
            Array.empty

            (*2*)
            [|
                ForAll (
                    x,
                    ForAll (
                        y,
                        Implication (
                            Exists (
                                z,
                                Formula (loves, [| Term y; Term z |])),
                            Formula (loves, [| Term x; Term y |]))))
            |],
            InferenceRule.Premise,
            Array.empty

            (*3*)
            [|
                Exists (
                    z,
                    Formula (loves, [| Term y; Term z |]))
            |],
            InferenceRule.UniversalElimination (Term y),
            [|1|]

            (*4*)
            [|
                ForAll (
                    y,
                    Implication (
                        Exists (
                            z,
                            Formula (loves, [| Term y; Term z |])),
                        Formula (loves, [| Term x; Term y |])))
            |],
            InferenceRule.UniversalElimination (Term x),
            [|2|]

            (*5*)
            [|
                Implication (
                    Exists (
                        z,
                        Formula (loves, [| Term y; Term z |])),
                    Formula (loves, [| Term x; Term y |]))
            |],
            InferenceRule.UniversalElimination (Term y),
            [|4|]

            (*6*)
            [|
                Formula (loves, [| Term x; Term y |])
            |],
            InferenceRule.implicationElimination,
            [|5; 3|]

            (*7*)
            [|
                ForAll (
                    y,
                    Formula (loves, [| Term x; Term y |]))
            |],
            InferenceRule.UniversalIntroduction y,
            [|6|]

            (*8*)
            [|
                ForAll (
                    x,
                    ForAll (
                        y,
                        Formula (loves, [| Term x; Term y |])))
            |],
            InferenceRule.UniversalIntroduction x,
            [|7|]
        |] |> this.Prove

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_03
    [<TestMethod>]
    member __.ExistentialIntroduction() =

        let jill = Term.constant "jill"
        let hates = Predicate ("hates", 2)
        let x = Variable "x"

        // introduce x for jill in hates(jill, jill)
        let formulaStrs =
            Formula (hates, [| jill; jill |])
                |> InferenceRule.existentialIntroduction jill x
                |> Seq.map (fun formula -> formula.ToString())
                |> set
        Assert.AreEqual(
            set [
                "∃x.hates(x, x)"
                "∃x.hates(jill, x)"
                "∃x.hates(x, jill)"
            ],
            formulaStrs)

        // introduce x for jill in ∃x.hates(jill, x)
        let formulaStrs =
            Exists (
                x,
                Formula (
                    hates,
                    [| jill; Term x |]))
                |> InferenceRule.existentialIntroduction jill x
                |> Array.map (fun formula -> formula.ToString())
        Assert.AreEqual(0, formulaStrs.Length)   // ∃x.∃x.hates(x, x)) is invalid

        // introduce y for f(x) in ∀x.hates(x, f(x))
        let fx =
            Application (
                Function ("f", 1),
                [| Term x |])
        let y = Variable "y"
        let formula =
            ForAll (
                x,
                Formula (
                    hates,
                    [| Term x; fx |]))
        let formulas =
            formula
                |> InferenceRule.existentialIntroduction fx y
        Assert.AreEqual(0, formulas.Length)   // ∃y.∀x.hates(x, y) is invalid

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_07
    [<TestMethod>]
    member this.QuantifiedProof2() =

        let x = Variable "x"
        let y = Variable "y"
        let p = Predicate ("p", 2)
        let q = Predicate ("q", 1)
        let skolemFunction =
            Skolem.createFunction 1
        let skolemTerm =
            Application (skolemFunction, [| Term x |])

        [|
            (*1*)
            [|
                ForAll (
                    x,
                    ForAll (
                        y,
                        Implication (
                            Formula (
                                p,
                                [| Term x; Term y |]),
                            Formula (
                                q,
                                [| Term x |]))))
            |],
            InferenceRule.Premise,
            Array.empty

            (*2*)
            [|
                Exists (
                    y,
                    Formula (
                        p,
                        [| Term x; Term y |]))
            |],
            InferenceRule.Assumption,
            Array.empty

            (*3*)
            [|
                Formula (
                    p,
                    [| Term x; skolemTerm |])
            |],
            InferenceRule.ExistentialElimination skolemFunction,
            [| 2 |]

            (*4*)
            [|
                ForAll (
                    y,
                    Implication (
                        Formula (
                            p,
                            [| Term x; Term y |]),
                        Formula (
                            q,
                            [| Term x |])))
            |],
            InferenceRule.UniversalElimination (Term x),
            [| 1 |]

            (*5*)
            [|
                Implication (
                    Formula (
                        p,
                        [| Term x; skolemTerm |]),
                    Formula (
                        q,
                        [| Term x |]))
            |],
            InferenceRule.UniversalElimination skolemTerm,
            [| 4 |]

            (*6*)
            [|
                Formula (
                    q,
                    [| Term x |])
            |],
            InferenceRule.implicationElimination,
            [| 3; 5 |]

            (*7*)
            [|
                Implication (
                    Exists (
                        y,
                        Formula (
                            p,
                            [| Term x; Term y |])),
                    Formula (
                        q,
                        [| Term x |]))
            |],
            InferenceRule.ImplicationIntroduction,
            [| 2; 6 |]

            (*8*)
            [|
                ForAll (
                    x,
                    Implication (
                        Exists (
                            y,
                            Formula (
                                p,
                                [| Term x; Term y |])),
                        Formula (
                            q,
                            [| Term x |])))
            |],
            InferenceRule.UniversalIntroduction x,
            [| 7 |]

        |] |> this.Prove

    [<TestMethod>]
    member this.QuantifiedProof3() =

        let x = Variable "x"
        let y = Variable "y"
        let p = Predicate ("p", 2)
        let q = Predicate ("q", 1)

        [|
            (*1*)
            [|
                ForAll (
                    x,
                    Implication (
                        Exists (
                            y,
                            Formula (
                                p,
                                [| Term x; Term y |])),
                        Formula (
                            q,
                            [| Term x |])))
            |],
            InferenceRule.Premise,
            Array.empty

            (*2*)
            [|
                Formula (
                    p,
                    [| Term x; Term y |])
            |],
            InferenceRule.Assumption,
            Array.empty

            (*3*)
            [|
                Exists (
                    y,
                    Formula (
                        p,
                        [| Term x; Term y |]))
            |],
            InferenceRule.ExistentialIntroduction (Term y, y),
            [| 2 |]

            (*4*)
            [|
                Implication (
                    Exists (
                        y,
                        Formula (
                            p,
                            [| Term x; Term y |])),
                    Formula (
                        q,
                        [| Term x |]))
            |],
            InferenceRule.UniversalElimination (Term x),
            [| 1 |]

            (*5*)
            [|
                Formula (
                    q,
                    [| Term x |])
            |],
            InferenceRule.implicationElimination,
            [| 4; 3 |]

            (*6*)
            [|
                Implication (
                    Formula (
                        p,
                        [| Term x; Term y |]),
                    Formula (
                        q,
                        [| Term x |]))
            |],
            InferenceRule.ImplicationIntroduction,
            [| 2; 5 |]

            (*7*)
            [|
                ForAll (
                    y,
                    Implication (
                        Formula (
                            p,
                            [| Term x; Term y |]),
                        Formula (
                            q,
                            [| Term x |])))
            |],
            InferenceRule.UniversalIntroduction y,
            [| 6 |]

            (*8*)
            [|
                ForAll (
                    x,
                    ForAll (
                        y,
                        Implication (
                            Formula (
                                p,
                                [| Term x; Term y |]),
                            Formula (
                                q,
                                [| Term x |]))))
            |],
            InferenceRule.UniversalIntroduction x,
            [| 7 |]

        |] |> this.Prove

    [<TestMethod>]
    member __.Parse() =

        let x = "x" |> Parser.run Parser.parseTerm
        Assert.AreEqual(Term (Variable "x"), x)

        let s_x = "s(x)" |> Parser.run Parser.parseTerm
        Assert.AreEqual(
            Application (
                Function ("s", 1),
                [| x |]),
            s_x)
