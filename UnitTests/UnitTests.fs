namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isMortal = Predicate ("Mortal", 1u)
    let x = [Variable "x"]

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

    [<TestMethod>]
    member __.Proof() =

        let p = MetaVariable.create "p"
        let q = MetaVariable.create "q"
        let r = MetaVariable.create "r"

        let steps =
            [|
                [
                    Implication (p, q)                                                      // 1
                    Implication (q, r)                                                      // 2
                ], InferenceRule.Premise, Array.empty
                [ p ], InferenceRule.Assumption, Array.empty                                // 3
                [ q ], InferenceRule.implicationElimination, [| 3; 1 |]                     // 4
                [ r ], InferenceRule.implicationElimination, [| 4; 2 |]                     // 5
                [ Implication (p, r) ], InferenceRule.ImplicationIntroduction, [| 3; 5 |]   // 6
            |]

        let proof =
            (Proof.empty, steps)
                ||> Seq.fold (fun acc (formulas, rule, indexes) ->
                    let proofOpt =
                        acc |> Proof.addSteps formulas rule indexes
                    match proofOpt with
                        | Some proof -> proof
                        | None ->
                            Assert.Fail()
                            Proof.empty)
        printfn "%A" proof
