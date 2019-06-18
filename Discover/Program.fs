namespace Discover

module Program =

    [<EntryPoint>]
    let main argv =

        System.Console.OutputEncoding <- System.Text.Encoding.Unicode

        let isMan = Predicate ("Man", 1u)
        let isMortal = Predicate ("Mortal", 1u)
        let x = Variable "x"
        let formulas =
            [
                And (
                    Implication (
                        Holds (isMan, [x]),
                        Holds (isMortal, [x])),
                    Holds (isMan, [x]))
                And (
                    Implication (
                        Holds (isMan, [x]),
                        Holds (isMortal, [x])),
                    Not (Holds (isMortal, [x])))
            ]
        let rules =
            [
                InferenceRule.modusPonens
                InferenceRule.modusTollens
            ]
        for formula in formulas do
            printfn "%A" formula
            for (antecedent, consequent) in rules do
                printfn "   %A => %A" antecedent consequent
                match InferenceRule.unify antecedent formula with
                    | Ok substitutions ->
                        printfn "      %A" substitutions
                        let result = InferenceRule.substitute consequent substitutions
                        printfn "      %A" result
                    | Error msg ->
                        printfn "      Error: %s" msg

        0
