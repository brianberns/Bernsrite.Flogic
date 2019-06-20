namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isMortal = Predicate ("Mortal", 1u)
    let x = [Variable "x"]

    [<TestMethod>]
    member __.ImplicationElimination() =
        Assert.AreEqual(
            Holds (isMortal, x) |> Some,
            InferenceRule.implicationElimination
                |> InferenceRule.tryApply
                    [|
                        Implication (
                            Holds (isMan, x),
                            Holds (isMortal, x))
                        Holds (isMan, x)
                    |])

    [<TestMethod>]
    member __.ImplicationCreation() =
        let bindingsOpt =
            InferenceRule.implicationCreation.Premises
                |> Schema.bind
                    [|
                        Implication (
                            Holds (isMan, x),
                            Holds (isMortal, x))
                        Holds (isMan, x)
                    |]
        printfn "%A" bindingsOpt
