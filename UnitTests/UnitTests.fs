namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isMortal = Predicate ("Mortal", 1u)
    let x = [Term (Variable "x")]

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

    member __.StartPropositionalProof() =

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

        (Proof.empty, steps)
            ||> Seq.fold (fun acc (formulas, rule, indexes) ->
                let proofOpt =
                    acc |> Proof.tryAddSteps formulas rule indexes
                match proofOpt with
                    | Some proof -> proof
                    | None ->
                        Assert.Fail()
                        Proof.empty)

    /// http://intrologic.stanford.edu/public/section.php?section=section_04_03
    [<TestMethod>]
    member this.ValidPropositionalProof1() =
        let proof = this.StartPropositionalProof()
        printfn "%A" proof
        Assert.IsTrue(proof |> Proof.isComplete)

    /// http://intrologic.stanford.edu/public/section.php?section=section_04_03
    [<TestMethod>]
    member this.InvalidPropositionalProof() =
        let proofOpt =
            this.StartPropositionalProof()
                |> Proof.tryAddSteps
                    [ MetaVariable.create "r" ]
                    InferenceRule.implicationElimination
                    [| 2; 4 |]
        Assert.AreEqual(None, proofOpt)

    /// http://intrologic.stanford.edu/public/section.php?section=section_04_03
    [<TestMethod>]
    member __.ValidPropositionalProof2() =

        let p = MetaVariable.create "p"
        let q = MetaVariable.create "q"
        let reiteration =
            Ordinary {
                Premises = [| p |]
                Conclusions = [| p |]
                Name = "Reiteration"
            }

        let steps =
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
            |]

        let proof =
            (Proof.empty, steps)
                ||> Seq.fold (fun acc (formulas, rule, indexes) ->
                    let proofOpt =
                        acc |> Proof.tryAddSteps formulas rule indexes
                    match proofOpt with
                        | Some proof -> proof
                        | None ->
                            Assert.Fail()
                            Proof.empty)
        printfn "%A" proof
        Assert.IsTrue(proof |> Proof.isComplete)

    [<TestMethod>]
    member __.UniversalIntroduction() =

        let x = Variable "x"
        let p = Formula (Predicate ("p", 1u), [Term x])
        let q = Formula (Predicate ("q", 1u), [Term x])

        let conclusions =
            UniversalIntroduction (x, [| p |])
                |> InferenceRule.apply [| q |]
        Assert.AreEqual(0, conclusions.Length)

        let conclusions =
            UniversalIntroduction (x, [| |])
                |> InferenceRule.apply [| Implication (p, q) |]
        Assert.AreEqual(1, conclusions.Length)
        Assert.AreEqual(1, conclusions.[0].Length)
        Assert.AreEqual(
            "∀x.(p(x) -> q(x))",
            conclusions.[0].[0].ToString())

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
                        [Term x; Term y])))
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
