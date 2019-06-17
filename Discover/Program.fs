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
        let (template, _) = InferenceRule.modusPonens
        let results = InferenceRule.unify template formula

        printfn "%A" template
        printfn "%A" formula
        for (name, form) in results do
            printfn "%s: %A" name form

        0
