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
                            Holds (isMan, x),
                            Holds (isMortal, x))
                        Holds (isMan, x)
                    |]
        Assert.AreEqual(1, conclusions.Length)
        Assert.AreEqual(1, conclusions.[0].Length)
        Assert.AreEqual(Holds (isMortal, x), conclusions.[0].[0])

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
                Holds (isMan, x)
                Holds (isMortal, x)
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

    /// http://intrologic.stanford.edu/public/section.php?section=section_08_02
    [<TestMethod>]
    member __.UniversalElimination() =

        let formula =
            let x = Variable "x"
            let y = Variable "y"
            let hates = Predicate ("hates", 2u)
            ForAll (
                x,
                Exists (
                    y,
                    Holds (
                        hates,
                        [Term x; Term y])))
        Assert.AreEqual(
            "∀x.∃y.hates(x, y)", formula.ToString())

        let newFormulaOpt =
            let jane = Variable "jane"
            formula
                |> InferenceRule.tryUniversalElimination (Term jane)
        Assert.AreEqual(
            Some "∃y.hates(jane, y)",
            newFormulaOpt |> Option.map (fun nf -> nf.ToString()))

        let newFormulaOpt =
            let y = Variable "y"
            formula
                |> InferenceRule.tryUniversalElimination (Term y)
        Assert.AreEqual(None, newFormulaOpt)
