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
                    clause
                        |> Clause.toLiterals
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
    member __.Deconflict() =
        let parser = Parser.makeParser ["0"]
        let clause1 =
            "((=(x', y) | =(x', y')) | =(0, s(y')))"
                |> Parser.run parser
                |> Clause.toClauses
                |> Seq.exactlyOne
        let clause2 =
            clause1
                |> Clause.map (fun literal ->
                    { literal with IsPositive = not literal.IsPositive})
        printfn "%A" clause1
        printfn "%A" clause2
        let pairs = Clause.resolve clause1 clause2
        for (resolvent, subst) in pairs do
            printfn ""
            printfn "%A" resolvent
            printfn "   %A" subst
        Assert.AreEqual(9, pairs.Length)

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
                        Bindings =
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
        let proofOpt = LinearResolution.tryProve premises goal
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof ->
                Assert.AreEqual(2, (proof.Derivation.Object :?> LinearResolutionDerivation).Steps.Length)
            | _ -> Assert.Fail()

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
        let proofOpt = LinearResolution.tryProve premises goal
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof ->
                Assert.AreEqual(7, (proof.Derivation.Object :?> LinearResolutionDerivation).Steps.Length)
            | _ -> Assert.Fail()

    [<TestMethod>]
    /// https://pdfs.semanticscholar.org/58e9/db343f70a3d2342a73c4376ce33e4252166d.pdf
    member __.Resolve3() =
        let parser = Parser.makeParser Array.empty
        let goal = "((((p∧q) ∨ (p∧¬q)) ∨ (¬p∧q)) ∨ (¬p∧¬q))" |> Parser.run parser
        let proofOpt = LinearResolution.tryProve Array.empty goal
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof -> Assert.IsTrue(proof.Result)
            | _ -> Assert.Fail()

    /// This test requires factoring.
    (*
    [<TestMethod>]
    member __.Factoring() =
        let parser = Parser.makeParser Array.empty
        let goalClauses =
            [|
                "(p(x) | p(y))"
                "(¬p(u) | ¬p(v))"
            |] |> Array.map (fun str ->
                str
                    |> Parser.run parser
                    |> Clause.toClauses
                    |> Seq.exactlyOne)
        let goalClause = goalClauses.[0]
        let config =
            {
                MaxDepth = 60
                MaxLiteralCount = 10
                MaxSymbolCount = 100
            }
        let derivationOpt =
            LinearResolutionDerivation.create
                goalClauses goalClause
                    |> LinearResolution.search config
        printfn "%A" derivationOpt
        Assert.IsTrue(derivationOpt.IsSome)
    *)

    [<TestMethod>]
    member __.Induction1() =
        let language =
            Language.create
                [| Constant.create "a" |]
                [| Function.create "f" 1 |]
                [| Predicate.create "P" 1 |]
        let parse = Language.parse language
        let system =
            {
                Language = language
                Axioms =
                    [|
                        "P(a)"
                        "∀x.(P(x) -> P(f(x)))"
                    |] |> Array.map parse
            }
        for axiom in system.Axioms do
            printfn "%A" axiom
            for clause in axiom |> Clause.toClauses do
                printfn "   %A" clause
        let proofOpt =
            parse "∀x.P(x)"
                |> System.tryProve system Array.empty
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof -> Assert.IsTrue(proof.Result)
            | _ -> Assert.Fail()

    [<TestMethod>]
    member __.Induction2() =

        let theory =
            {
                Language =
                    Language.create
                        [| Peano.zero |]
                        [| Peano.successor |]
                        [| Predicate.create "p" 1 |]
                Axioms = Array.empty
            }
        let parse = Language.parse theory.Language

        let premises =
            [|
                "∀x.(p(x) ⇒ p(s(s(x))))"
                "p(0)"
                "p(s(0))"
            |] |> Array.map parse
        let goal = parse "∀x.(p(x) ∧ p(s(x)))"
        let proofOpt =
            goal
                |> System.tryProve theory premises
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof -> Assert.IsTrue(proof.Result)
            | _ -> Assert.Fail()

        let premises' =
            [|
                yield! premises
                yield goal
            |]
        let proofOpt =
            parse "∀x.p(x)"   // to-do: prove this directly from initial premises
                |> System.tryProve theory premises'
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof -> Assert.IsTrue(proof.Result)
            | _ -> Assert.Fail()

[<TestClass>]
type Peano() =

    member __.Test(goalStr, ?flagOpt, ?premiseStrsOpt) =
        let flag = defaultArg flagOpt true
        let premiseStrs = defaultArg premiseStrsOpt Seq.empty
        let parse = Language.parse Peano.language
        let premises =
            premiseStrs
                |> Seq.map parse
        let proofOpt =
            goalStr
                |> parse
                |> System.tryProve Peano.theory premises
        printfn "%A" proofOpt
        match proofOpt with
            | Some proof -> Assert.AreEqual(flag, proof.Result)
            | _ -> Assert.Fail()

    [<TestMethod>]
    member this.EqualityReflexive() =
        this.Test("∀x.=(x, x)")

    [<TestMethod>]
    member this.EqualitySymmetric() =
        this.Test("∀x.∀y.(=(x, y) ⇒ =(y, x))")

    [<TestMethod>]
    member this.EqualityTransitive() =
        this.Test("∀x.∀y.∀z.((=(x, y) ∧ =(y, z)) ⇒ =(x, z))")

    [<TestMethod>]
    member this.EqualityFalse() =
        this.Test("∀x.∀y.=(x, y)", false)

    [<TestMethod>]
    member this.Successor1() =
        this.Test("∀x.∀y.(=(x, y) <-> =(s(x), s(y)))")
        this.Test ("(=(x, y) <-> =(s(x), s(y)))")

    [<TestMethod>]
    member this.Successor2() =
        this.Test("∀x.~=(s(x), 0)", true)
        this.Test("∃x.=(s(x), 0)", false)

    [<TestMethod>]
    member this.Successor3() =
        this.Test("∀x.∀y.=(+(x,s(y)), s(+(x,y)))")

    [<TestMethod>]
    member this.AdditionIdentity() =
        this.Test("∀x.=(+(x,0), x)")
        this.Test("∀x.=(+(0,x), x)")

    (*
    [<TestMethod>]
    member this.AdditionCommutative() =
        this.Test("∀x.∀y.=(+(x,y), +(y,x))",
            premiseStrsOpt = [
                "∀x.=(+(x,0), x)"
                "∀x.=(+(0,x), x)"
            ])

    [<TestMethod>]
    member this.AdditionCancellative() =
        this.Test("∀x.∀y.∀z.(=(+(x,z), +(y,z)) ⇒ =(x, y))")

    [<TestMethod>]
    member this.AdditionAssociative() =
        this.Test("∀z.∀x.∀y.=(+(+(x,y),z), +(x,+(y,z)))")
    *)
