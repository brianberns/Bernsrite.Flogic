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

type Package =
    {
        Values : Value[]
        Functions : Function[]
    }

module Natural =

    let zero =
        BasicValue {
            Signature = BasicSignature "Natural"
            Value = "0"
        }

    let typ = zero.Type

    let succ =
        {
            Signature =
                {
                    InputType = typ
                    OutputType = typ
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

    let package =
        {
            Values = [| zero |]
            Functions = [| succ |]
        }

[<EntryPoint>]
let main argv =
    0
