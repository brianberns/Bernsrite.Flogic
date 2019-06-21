namespace Discover

/// Ordinary rule of inference (i.e. not structured).
[<StructuredFormatDisplay("{Name}")>]
type InferenceRule =
    {
        Premises : Schema[]
        Conclusions : Schema[]
        Name : string
    }

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
        {
            Premises = [| p; q |]
            Conclusions = [| And (p, q) |]
            Name = "andIntroduction"
        }

    /// P & Q
    /// -----
    /// P
    let andEliminationLeft =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| p |]
            Name = "andEliminationLeft"
        }

    /// P & Q
    /// -----
    /// Q
    let andEliminationRight =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| q |]
            Name = "andEliminationRight"
        }

    /// P
    /// -----
    /// P | Q
    let orIntroductionLeft =
        {
            Premises = [| p |]
            Conclusions = [| Or (p, q) |]
            Name = "orIntroductionLeft"
        }

    /// Q
    /// -----
    /// P | Q
    let orIntroductionRight =
        {
            Premises = [| q |]
            Conclusions = [| Or (p, q) |]
            Name = "orIntroductionRight"
        }

    /// P | Q
    /// P -> R
    /// Q -> R
    /// -----
    /// R
    let orElimination =
        {
            Premises =
                [|
                    Or (p, q)
                    Implication (p, r)
                    Implication (q, r)
                |]
            Conclusions = [| r |]
            Name = "orElimination"
        }

    /// P -> Q
    /// P -> ~Q
    /// -----
    /// ~P
    let notIntroduction =
        {
            Premises =
                [|
                    Implication (p, q)
                    Implication (p, Not q)
                |]
            Conclusions = [| Not p |]
            Name = "notIntroduction"
        }

    /// ~~P
    /// -----
    /// P
    let notElimination =
        {
            Premises = [| Not (Not p) |]
            Conclusions = [| p |]
            Name = "notElimination"
        }

    /// Implication introduction is a structured rule:
    ///
    /// P |- Q  (i.e. Q can be proved from P)
    /// ------
    /// P -> Q
    ///
    /// Implementation is programmatic instead of declarative.

    /// P -> Q
    /// P
    /// ------
    /// Q
    ///
    /// AKA modus ponens.
    let implicationElimination =
        {
            Premises = [| Implication (p, q); p |]
            Conclusions = [| q |]
            Name = "implicationElimination"
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalIntroduction =
        {
            Premises =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
            Conclusions = [| Biconditional (p, q) |]
            Name = "biconditionalIntroduction"
        }

    /// P -> Q
    /// Q -> P
    /// -------
    /// P <-> Q
    let biconditionalElimination =
        {
            Premises = [| Biconditional (p, q) |]
            Conclusions =
                [|
                    Implication (p, q)
                    Implication (q, p)
                |]
            Name = "biconditionalElimination"
        }

    let allRules =
        [|
            andIntroduction
            andEliminationLeft
            andEliminationRight

            orIntroductionLeft
            orIntroductionRight
            orElimination

            notIntroduction
            notElimination

            implicationElimination

            biconditionalIntroduction
            biconditionalElimination
        |]

    /// Finds all possible applications of the given rule to the
    /// given formulas.
    let apply formulas rule =
        Schema.bind formulas rule.Premises
            |> Array.map (fun binding ->
                rule.Conclusions
                    |> Array.map (Schema.substitute binding))
