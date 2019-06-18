namespace Discover

module Program =

    [<EntryPoint>]
    let main argv =

        System.Console.OutputEncoding <- System.Text.Encoding.Unicode

        let isMan = Predicate ("Man", 1u)
        let isWoman = Predicate ("Woman", 1u)
        let isHuman = Predicate ("Human", 1u)
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
                And (
                    Implication (
                        Holds (isMan, [x]),
                        Holds (isHuman, [x])),
                    Implication (
                        Holds (isHuman, [x]),
                        Holds (isMortal, [x])))
                And (
                    Or (
                        Holds (isMan, [x]),
                        Holds (isWoman, [x])),
                    Not (Holds (isMan, [x])))
            ]
        let rules =
            [
                InferenceRule.modusPonens
                InferenceRule.modusTollens
                InferenceRule.hypotheticalSyllogism
                InferenceRule.disjunctiveSyllogism
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
