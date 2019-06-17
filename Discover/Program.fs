namespace Discover

module Program =

    [<EntryPoint>]
    let main argv =

        System.Console.OutputEncoding <- System.Text.Encoding.Unicode

        let isMan = Predicate ("Man", 1u)
        let isMortal = Predicate ("Mortal", 1u)
        let x = Variable "x"
        let formula =
            And (
                Implication (
                    Holds (isMan, [x]),
                    Holds (isMortal, [x])),
                Holds (isMan, [x]))
        let (antecedent, consequent) = InferenceRule.modusPonens
        let substitutions = InferenceRule.unify antecedent formula
        let result = InferenceRule.substitute consequent substitutions

        printfn "%A" formula
        printfn "%A" result

        0
