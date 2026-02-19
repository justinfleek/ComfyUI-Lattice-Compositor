let Core = ./Core.dhall
let Resource = ./Resource.dhall

-- Placeholder for JSON Schema (content addressed)
let JsonSchema = { _type : Text }

let Tool =
  { name : Text
  , description : Text
  , input : Core.Hash JsonSchema
  , output : Core.Hash JsonSchema
  , idempotent : Bool
  , coeffects : Resource.Coeffects
  }

let ThinkingInteraction =
  < ThinkingBeforeCall
  | ThinkingAroundCall
  | NoThinking
  >

let MultiCallBehavior =
  < RepeatedTags
  | ArrayInSingleTag
  | NotSupported
  >

let EosBehavior =
  < EmitAfterToolCall
  | EmitAfterMessage
  | EmitAfterBoth
  | ModelDecides
  >

let ToolFormat =
  { call_prefix : List Text
  , call_suffix : List Text
  , result_prefix : List Text
  , result_suffix : List Text
  , thinking_interaction : ThinkingInteraction
  , multi_call : MultiCallBehavior
  , eos_behavior : EosBehavior
  , test_vectors : Core.Hash { _type : Text }
  }

in { Tool, ToolFormat, ThinkingInteraction, MultiCallBehavior, EosBehavior }
