namespace Discover

/// https://stackoverflow.com/questions/7818277/is-there-a-standard-option-workflow-in-f
type OptionBuilder() =
    member __.Bind(v, f) = Option.bind f v
    member __.Return(v) = Some v
    member __.ReturnFrom(o) = o
    member __.Zero() = None

[<AutoOpen>]
module OptionAutoOpen =

    /// Build for option monad.
    let opt = OptionBuilder()
