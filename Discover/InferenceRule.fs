namespace Discover

/// Ordinary rule of inference (i.e. not structured).
type InferenceRule =
    {
        Premises : Schema[]
        Conclusions : Schema[]
    }

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
        }

    /// P & Q
    /// -----
    /// P
    let andEliminationLeft =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| p |]
        }

    /// P & Q
    /// -----
    /// Q
    let andEliminationRight =
        {
            Premises = [| And (p, q) |]
            Conclusions = [| q |]
        }

    /// P
    /// -----
    /// P | Q
    let orIntroductionLeft =
        {
            Premises = [| p |]
            Conclusions = [| Or (p, q) |]
        }

    /// Q
    /// -----
    /// P | Q
    let orIntroductionRight =
        {
            Premises = [| q |]
            Conclusions = [| Or (p, q) |]
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
        }

    /// ~~P
    /// -----
    /// P
    let notElimination =
        {
            Premises = [| Not (Not p) |]
            Conclusions = [| p |]
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
