namespace Discover

/// Ordinary rule of inference.
[<StructuredFormatDisplay("{Name}")>]
type OrdinaryInferenceRule =
    {
        Premises : Schema[]
        Conclusions : Schema[]
        Name : string
    }

    override this.ToString() = this.Name

module OrdinaryInferenceRule =

    /// Finds all possible applications of the given rule to the
    /// given formulas.
    let apply formulas rule =
        Schema.bind formulas rule.Premises
            |> Array.map (fun binding ->
                rule.Conclusions
                    |> Array.map (Schema.apply binding))

[<StructuredFormatDisplay("{Name}")>]
type InferenceRule =

    /// Top-level premise.
    | Premise

    /// Ordinary rule.
    | Ordinary of OrdinaryInferenceRule

    /// Sub-proof assumption.
    | Assumption

    /// Discharges an assumption, P.
    ///
    /// P |- Q  (i.e. Q can be proved from P)
    /// ------
    /// P -> Q
    | ImplicationIntroduction

    /// P
    /// ----
    /// ∀v.P where v doesn't appear free in both P and an active
    /// assumption.
    | UniversalIntroduction of (Variable * Formula[] (*assumptions*))

    /// Reasons from the general to the specific.
    ///
    /// ∀v.P(v)
    /// --------
    /// P(t/v) where term t is "free for" variable v in P and P(t/v)
    /// is the substituion of t for v in P.
    | UniversalElimination of Term

    /// Display string.
    member this.Name =
        match this with
            | Ordinary oir -> oir.Name
            | Premise -> "Premise"
            | Assumption -> "Assumption"
            | ImplicationIntroduction -> "Implication introduction"
            | UniversalIntroduction _ -> "Universal introduction"
            | UniversalElimination term ->
                sprintf "Universal elimination (%A)" term

    /// Display string.
    override this.ToString() = this.Name

module InferenceRule =

    /// Metavariables.
    let private p, private q, private r =
        MetaVariable.create "P",
        MetaVariable.create "Q",
        MetaVariable.create "R"

    /// P
    /// Q
    /// -----
    /// P & Q
    let andIntroduction =
        Ordinary {
            Premises = [| p; q |]
            Conclusions = [| And (p, q) |]
            Name = "And introduction"
        }

    /// P & Q
    /// -----
    /// P
    let andEliminationLeft =
        Ordinary {
            Premises = [| And (p, q) |]
            Conclusions = [| p |]
            Name = "And elimination (left)"
        }

    /// P & Q
    /// -----
    /// Q
    let andEliminationRight =
        Ordinary {
            Premises = [| And (p, q) |]
            Conclusions = [| q |]
            Name = "And elimination (right)"
        }

    /// P
    /// -----
    /// P | Q
    let orIntroductionLeft =
        Ordinary {
            Premises = [| p |]
            Conclusions = [| Or (p, q) |]
            Name = "Or introduction (left)"
        }

    /// Q
    /// -----
    /// P | Q
    let orIntroductionRight =
        Ordinary {
            Premises = [| q |]
            Conclusions = [| Or (p, q) |]
            Name = "Or introduction (right)"
        }

    /// P | Q
    /// P -> R
    /// Q -> R
    /// -----
    /// R
    let orElimination =
        Ordinary {
            Premises =
                [|
                    Or (p, q)
                    Implication (p, r)
                    Implication (q, r)
                |]
            Conclusions = [| r |]
            Name = "Or elimination"
        }

    /// P -> Q
    /// P -> ~Q
    /// -----
    /// ~P
    let notIntroduction =
        Ordinary {
            Premises =
                [|
                    Implication (p, q)
                    Implication (p, Not q)
                |]
            Conclusions = [| Not p |]
            Name = "Not introduction"
        }

    /// ~~P
    /// -----
    /// P
    let notElimination =
        Ordinary {
            Premises = [| Not (Not p) |]
            Conclusions = [| p |]
            Name = "Not elimination"
        }

    /// Modus ponens.
    ///
    /// P -> Q
    /// P
    /// ------
    /// Q
    let implicationElimination =
        Ordinary {
            Premises = [| Implication (p, q); p |]
            Conclusions = [| q |]
            Name = "Implication elimination"
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalIntroduction =
        Ordinary {
            Premises =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
            Conclusions = [| Biconditional (p, q) |]
            Name = "Biconditional introduction"
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalElimination =
        Ordinary {
            Premises = [| Biconditional (p, q) |]
            Conclusions =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
            Name = "Biconditional elimination"
        }

    /// Fitch rules: http://intrologic.stanford.edu/glossary/fitch_system.html
    let allRules =
        [|
            Premise
            Assumption

            andIntroduction
            andEliminationLeft
            andEliminationRight

            orIntroductionLeft
            orIntroductionRight
            orElimination

            notIntroduction
            notElimination

            implicationElimination
            ImplicationIntroduction

            biconditionalIntroduction
            biconditionalElimination
        |]

    /// Tries to introduce a universal quantification.
    let private tryUniversalIntroduction variable assumptions formula =
        let isValid =
            if formula |> Formula.isFree variable then
                assumptions
                    |> Seq.forall (
                        Formula.isFree variable >> not)
            else true
        if isValid then
            ForAll (variable, formula) |> Some
        else None

    /// Tries to instantiate a universal quantification.
    let private tryUniversalElimination term = function
        | ForAll (variable, formula)
            when formula |> Formula.isFreeFor term variable ->
                formula
                    |> Formula.substitute variable term
                    |> Some
        | _ -> None

    /// Finds all possible applications of the given rule to the
    /// given formulas.
    let apply formulas rule =

        let wrap formula =
            [|
                [| formula |]
            |]

        match rule with
            | Assumption
            | Premise ->
                [| formulas |]
            | Ordinary rule ->
                rule |> OrdinaryInferenceRule.apply formulas
            | ImplicationIntroduction ->
                if formulas.Length = 2 then
                    Implication (formulas.[0], formulas.[1]) |> wrap
                else Array.empty
            | UniversalIntroduction (variable, assumptions) ->
                if formulas.Length = 1 then
                    formulas.[0]
                        |> tryUniversalIntroduction variable assumptions
                        |> Option.map wrap
                        |> Option.defaultValue Array.empty
                else Array.empty
            | UniversalElimination term ->
                if formulas.Length = 1 then
                    formulas.[0]
                        |> tryUniversalElimination term
                        |> Option.map wrap
                        |> Option.defaultValue Array.empty
                else Array.empty
