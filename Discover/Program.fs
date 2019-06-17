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
        let result =
            InferenceRule.unify template formula
        printfn "%A" result

        0
