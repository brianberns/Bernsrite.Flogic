namespace Discover

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    let isMan = Predicate ("Man", 1u)
    let isWoman = Predicate ("Woman", 1u)
    let isHuman = Predicate ("Human", 1u)
    let isMortal = Predicate ("Mortal", 1u)
    let x = [Variable "x"]

    let test formula expectedRule expectedFormula =

        for rule in InferenceRule.allRules do
            let result = rule |> InferenceRule.apply formula
            if rule = expectedRule then
                Assert.AreEqual(Some expectedFormula, result |> Result.tryGet)
            else
                Assert.IsTrue(result |> Result.isError)

        let proofOpt =
            InferenceRule.allRules
                |> InferenceRule.prove formula expectedFormula
        match proofOpt with
            | Some proof ->
                for step in proof do
                    printfn "%A" step
            | None -> Assert.Fail()

    [<TestMethod>]
    member __.ModusPonens() =
        test
            (And (
                Implication (
                    Holds (isMan, x),
                    Holds (isMortal, x)),
                Holds (isMan, x)))
            InferenceRule.modusPonens
            (Holds (isMortal, x))

    [<TestMethod>]
    member __.ModusTollens() =
        test
            (And (
                Implication (
                    Holds (isMan, x),
                    Holds (isMortal, x)),
                Not (Holds (isMortal, x))))
            InferenceRule.modusTollens
            (Not (Holds (isMan, x)))

    [<TestMethod>]
    member __.HypotheticalSyllogism() =
        test
            (And (
                Implication (
                    Holds (isMan, x),
                    Holds (isHuman, x)),
                Implication (
                    Holds (isHuman, x),
                    Holds (isMortal, x))))
            InferenceRule.hypotheticalSyllogism
            (Implication (
                Holds (isMan, x),
                Holds (isMortal, x)))

    [<TestMethod>]
    member __.DisjunctiveSyllogism() =
        test
            (And (
                Or (
                    Holds (isMan, x),
                    Holds (isWoman, x)),
                Not (Holds (isMan, x))))
            InferenceRule.disjunctiveSyllogism
            (Holds (isWoman, x))
