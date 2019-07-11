namespace Bernsrite.Flogic

open System
open System.Text.RegularExpressions

open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type UnitTest() =

    [<TestMethod>]
    member __.ClausalNormalForm() =

        let parser = Parser.makeParser Array.empty

            // Anyone who loves all animals, is in turn loved by someone
            // https://en.wikipedia.org/wiki/Conjunctive_normal_form
        let clauses =
            "∀x.(∀y.(Animal(y) -> Loves(x, y)) -> ∃y.Loves(y, x))"
                |> Parser.run parser
                |> Clause.toClauses
                |> Seq.map (fun clause ->
                    clause.Literals
                        |> Seq.map Literal.toString
                        |> Seq.toArray)
                |> Seq.toArray
        Assert.AreEqual(2, clauses.Length)
        Assert.AreEqual(2, clauses.[0].Length)
        let groups00 =
            Regex
                .Match(
                    clauses.[0].[0],
                    "Animal\(skolem(\d+)\(x\)\)")
                .Groups
        Assert.AreEqual(2, groups00.Count)
        let groups01 =
            Regex
                .Match(
                    clauses.[0].[1],
                    "Loves\(skolem(\d+)\(x\), x\)")
                .Groups
        Assert.AreEqual(2, groups01.Count)
        Assert.AreNotEqual(groups00.[1].Value, groups01.[1].Value)
        Assert.AreEqual(clauses.[0].[1], clauses.[1].[1])
        let groups11 =
            Regex
                .Match(
                    clauses.[1].[0],
                    "~Loves\(x, skolem(\d+)\(x\)\)")
                .Groups
        Assert.AreEqual(2, groups11.Count)
        Assert.AreEqual(groups00.[1].Value, groups11.[1].Value)

        let inputs =
            [
                    // http://www.cs.miami.edu/home/geoff/Courses/COMP6210-10M/Content/FOFToCNF.shtml
                "∀Y.(∀X.(taller(Y,X) | wise(X)) => wise(Y))"
                "~∃X.(s(X) & q(X))"
                "∀X.(p(X) => (q(X) | r(X)))"
                "~∃X.(p(X) => ∃X.q(X))"
                "∀X.((q(X) | r(X)) => s(X))"
                "∃X.(p => f(X))"
                "∃X.(p <=> f(X))"
                "∀Z.∃Y.∀X.(f(X,Y) <=> (f(X,Z) & ~f(X,X)))"
                "∀X.∀Y.(q(X,Y) <=> ∀Z.(f(Z,X) <=> f(Z,Y)))"
                "∃X.(∃Y.(p(X,Y) & q(Y)) => ∃Z.(p(Z,X) & q(Z)))"
                "∀X.∃Y.((p(X,Y) <= ∀X.∃T.q(Y,X,T)) => r(Y))"
                "∀X.∀Z.(p(X,Z) => ∃Y.~(q(X,Y) | ~r(Y,Z)))"

                "(g ∧ (r ⇒ f))"
                "¬(g ∧ (r ⇒ f))"
                "∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y, z)))"
                "¬∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y, z)))"
            ]
        for input in inputs do
            let clauses =
                input
                    |> Parser.run parser
                    |> Clause.toClauses
            printfn ""
            printfn "%s" input
            for clause in clauses do
                printfn "%s" <| String.Join(" | ", clause)

    [<TestMethod>]
    member __.Unification() =
        let parseTerm, parseFormula = Parser.makeParsers [ "a"; "b" ]
        let inputs =
            [
                "P(x, y)", "P(f(z), x)", [
                    "x", "f(z)"
                    "y", "f(z)"
                ]
                "p(x, b)", "p(a, y)", [
                    "x", "a"
                    "y", "b"
                ]
                "p(x, x)", "p(a, y)", [
                    "x", "a"
                    "y", "a"
                ]
                "p(x)", "p(f(x))", [
                ]
            ]
        for input1, input2, expectedStrs in inputs do
            printfn ""
            printfn "%s, %s" input1 input2
            let actual =
                let parse = Parser.run parseFormula >> Literal.ofFormula
                Literal.tryUnify (parse input1) (parse input2)
            let expected =
                if expectedStrs.IsEmpty then
                    None
                else
                    Some {
                        SubstMap =
                            expectedStrs
                                |> Seq.map (fun (oldStr, newStr) ->
                                    let term = newStr |> Parser.run parseTerm
                                    oldStr, term)
                                |> Seq.toArray
                    }
            Assert.AreEqual(expected, actual)

    [<TestMethod>]
    member __.Resolve1() =
        let parser = Parser.makeParser Array.empty
        let premises =
            [|
                "∀x.∃y.loves(x,y)"
                "∀u.∀v.∀w.(loves(v,w) ⇒ loves(u,v))"
            |] |> Array.map (Parser.run parser)
        let goal = "∀x.∀y.loves(x,y)" |> Parser.run parser
        match Proof.tryLinearResolution premises goal with
            | Some proof ->
                printfn "%A" proof
                Assert.AreEqual(2, proof.Steps.Length)
            | None -> Assert.Fail()

    [<TestMethod>]
    member __.Resolve2() =
        let parser = Parser.makeParser ["harry"; "ralph"]
        let premises =
            [|
                "∀x.∀y.((h(x) ∧ d(y)) ⇒ f(x, y))"
                "∃y.(g(y) ∧ ∀z.(r(z) ⇒ f(y, z)))"
                "∀y.(g(y) ⇒ d(y))"
                "∀x.∀y.∀z.((f(x, y) ∧ f(y, z)) ⇒ f(x, z))"
                "h(harry)"
                "r(ralph)"
            |] |> Array.map (Parser.run parser)
        let goal = "f(harry, ralph)" |> Parser.run parser
        match Proof.tryLinearResolution premises goal with
            | Some proof ->
                printfn "%A" proof
                Assert.AreEqual(7, proof.Steps.Length)
            | None -> Assert.Fail()

    [<TestMethod>]
    member __.Induction() =
        let parse = Parser.run Peano.parser
        let premises =
            [|
                "∀y.+(0,y,y)"
                "∀x.∀y.∀z.(+(x,y,z) ⇒ +(s(x),y,s(z)))"
            |] |> Array.map parse
        let proofOpt =
            parse "∀x.+(x,0,x)"
                |> Proof.tryLinearInduction Peano.language premises
        match proofOpt with
            | Some (baseProof, inductiveProof) ->
                printfn "Base case:"
                printfn "%A" baseProof
                printfn "Inductive case:"
                printfn "%A" inductiveProof
            | None -> Assert.Fail()

    [<TestMethod>]
    member __.Peano() =
        let goalPairs =
            [|
                "∀x.∀y.(=(x,y) ⇒ =(y,x))", true
                "∀x.∀y.=(x,y)", false
                "(=(0, y) ⇒ =(0, s(y)))", false
                "∀y.(=(0, y) ⇒ =(0, s(y)))", false
                "∀x.∀y.=(x,y)", false
            |] |> Array.map (fun (str, flag) ->
                str |> Parser.run Peano.parser, flag)
        for (goal, flag) in goalPairs do
            let proofOpt =
                goal
                    |> Proof.tryProve Peano.language Peano.equalsAxioms
            Assert.AreEqual(flag, proofOpt.IsSome)
