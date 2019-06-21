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

        let proof = Proof.empty
        let proof =
            proof |> Proof.addSteps [||] None [
                Implication (p, q)
                Implication (q, r)
            ]
        let proof =
            proof |> Proof.addSteps [||] None [p]
        let proof =
            proof
                |> Proof.addSteps
                    [|3; 1|]
                    (Some InferenceRule.implicationElimination)
                    [q]
        printfn "%A" proof
