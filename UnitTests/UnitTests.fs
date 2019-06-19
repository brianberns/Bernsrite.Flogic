namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isMortal = Predicate ("Mortal", 1u)
    let x = [Variable "x"]

    let test formulas expectedRule expectedFormula =

        for rule in InferenceRule.allRules do
            let result = rule |> InferenceRule.tryApply formulas
            if rule = expectedRule then
                Assert.AreEqual(Some expectedFormula, result)
            else
                Assert.AreEqual(None, result)

    [<TestMethod>]
    member __.ModusPonens() =
        test
            [|
                Implication (
                    Holds (isMan, x),
                    Holds (isMortal, x))
                Holds (isMan, x)
            |]
            InferenceRule.implicationElimination
            (Holds (isMortal, x))
