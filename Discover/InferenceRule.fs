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
                    |> Array.map (Schema.substitute binding))

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

    member this.Name =
        match this with
            | Premise -> "Premise"
            | Ordinary oir -> oir.Name
            | Assumption -> "Assumption"
            | ImplicationIntroduction -> "Implication introduction"

    override this.ToString() = this.Name

module InferenceRule =

    /// Metavariables.
    let private p = MetaVariable.create "P"
    let private q = MetaVariable.create "Q"
    let private r = MetaVariable.create "R"

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

    /// P -> Q
    /// P
    /// ------
    /// Q
    ///
    /// AKA modus ponens.
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

    /// Finds all possible applications of the given rule to the
    /// given formulas.
    let apply formulas = function
        | Assumption
        | Premise ->
            [| formulas |]
        | Ordinary rule ->
            rule |> OrdinaryInferenceRule.apply formulas
        | ImplicationIntroduction ->
            if formulas.Length = 2 then
                [|
                    [| Implication (formulas.[0], formulas.[1]) |]
                |]
            else Array.empty
