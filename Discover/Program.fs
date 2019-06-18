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
        printfn "%A" formula

        let rules =
            [
                InferenceRule.modusPonens
                InferenceRule.modusTollens
            ]
        for (antecedent, consequent) in rules do
            printfn ""
            match InferenceRule.unify antecedent formula with
                | Ok substitutions ->
                    printfn "%A" substitutions
                    let result = InferenceRule.substitute consequent substitutions
                    printfn "%A" result
                | Error msg ->
                    printfn "%s" msg

        0
