type BasicSignature =
    | BasicSignature of string

type Type =
    | BasicType of BasicSignature
    | FunctionType of FunctionSignature
and FunctionSignature =
    {
        InputType : Type
        OutputType : Type
    }

type BasicValue =
    {
        Signature : BasicSignature
        Value : string
    }

type Value =
    | BasicValue of BasicValue
    | FunctionValue of Function
    member this.Type =
        match this with
            | BasicValue basicValue -> BasicType basicValue.Signature
            | FunctionValue func -> FunctionType func.Signature
and Function =
    {
        Signature : FunctionSignature
        Name : string
        Implementation : Value -> Value
    }

module Function =

    let apply (input : Value) func =
        assert(input.Type = func.Signature.InputType)
        func.Implementation(input)

    let (|.>) = apply

    let compose func1 func2 =
        {
            Signature =
                {
                    InputType = func1.Signature.InputType
                    OutputType = func2.Signature.OutputType
                }
            Name = sprintf "%s+%s" func1.Name func2.Name
            Implementation = fun input ->
                input
                    |.> func1
                    |.> func2
        }

    let (>.>) = compose

[<AutoOpen>]
module AutoOpen =

    let (|.>) = Function.(|.>)
    let (>.>) = Function.(>.>)

[<EntryPoint>]
let main argv =
    let naturalSignature = BasicSignature "natural"
    let naturalType = BasicType naturalSignature
    let zero =
        BasicValue {
            Signature = naturalSignature
            Value = "0"
        }
    let succ = 
        {
            Signature =
                {
                    InputType = naturalType
                    OutputType = naturalType
                }
            Name = "Successor"
            Implementation = function
                | BasicValue input ->
                    BasicValue {
                        input with
                            Value = sprintf "S(%s)" input.Value
                    }
                | FunctionValue _ -> failwith "Unexpected"
        }
    printfn "%A" (zero |.> succ |.> succ)
    printfn "%A" (zero |.> (succ >.> succ))
    0
