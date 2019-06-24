namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isMortal = Predicate ("Mortal", 1u)
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
        let p = Formula (Predicate ("p", 1u), [| Term x |])
        let q = Formula (Predicate ("q", 1u), [| Term x |])

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
                        Predicate ("hates", 2u),
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
        let loves = Predicate ("loves", 2u)

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
    /// Elliott Mendelson, Introduction to Mathematical Logic: Existential Rule E4
    [<TestMethod>]
    member __.ExistentialIntroduction() =

        let jill = Term.constant "jill"
        let hates = Predicate ("hates", 2u)
        let x = Variable "x"

        // hates(jill, jill)
        let formulaOpt =
            Formula (hates, [| jill; jill |])
                |> Formula.tryExistentialIntroduction jill x
        Assert.AreEqual(
            Some "∃x.hates(x, x)",
            formulaOpt
                |> Option.map (fun formula ->
                    formula.ToString()))
        // But what about:
        //    ∃y.hates(jill, y)
        //    ∃x.hates(x, jill)
        //    ∃x.∃y.hates(x, y)

        // introduce x for jill in ∃x.hates(jill, x)
        let formulaOpt =
            Exists (
                x,
                Formula (
                    hates,
                    [| jill; Term x |]))
                |> Formula.tryExistentialIntroduction jill x
        Assert.AreEqual(None, formulaOpt)   // ∃x.∃x.hates(x, x)) is invalid

        // introduce y for f(x) in ∀x.hates(x, f(x))
        let fx =
            Application (
                Function ("f", 1u),
                [| Term x |])
        let y = Variable "y"
        let formula =
            ForAll (
                x,
                Formula (
                    hates,
                    [| Term x; fx |]))
        let formulaOpt =
            formula
                |> Formula.tryExistentialIntroduction fx y
        Assert.AreEqual(None, formulaOpt)   // ∃y.∀x.hates(x, y) is invalid

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_07
    [<TestMethod>]
    member this.QuantifiedProof2() =

        let x = Variable "x"
        let y = Variable "y"
        let p = Predicate ("p", 2u)
        let q = Predicate ("q", 1u)
        let skolem =
            Application (
                Function ("[skolem1]", 1u),   // fix: caller must guess name of skolem function
                [| Term x |])

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
                    [| Term x; skolem |])
            |],
            InferenceRule.ExistentialElimination,
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
                        [| Term x; skolem |]),
                    Formula (
                        q,
                        [| Term x |]))
            |],
            InferenceRule.UniversalElimination skolem,
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
