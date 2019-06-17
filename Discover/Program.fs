namespace Discover

module Program =

    [<EntryPoint>]
    let main argv =

        let IsMan = Predicate ("IsMan", 1u)
        let IsMortal = Predicate ("IsMortal", 1u)
        let x = Variable "x"
        let formula =
            And (
                Implication (
                    IsTrue (IsMan, [x]),
                    IsTrue (IsMortal, [x])),
                IsTrue (IsMan, [x]))
        let (template, _) = InferenceRule.modusPonens
        let results =
            InferenceRule.unify template formula
        printfn "%s" <| formula.ToString()
        for (name, result) in results do
            printfn "%s: %s" name <| result.ToString()

        0
