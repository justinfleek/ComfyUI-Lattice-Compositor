let Core = ./Core.dhall
let Tokenizer = ./Tokenizer.dhall
let Tool = ./Tool.dhall

let Weights = { _type : Text }
let Architecture = { _type : Text }
let Vocab = { _type : Text }
let TestVectors = { _type : Text }

let Delimiters =
  { think_start : Optional Text
  , think_end : Optional Text
  , tool_start : Optional Text
  , tool_end : Optional Text
  , code_fence : Text
  }

let Model =
  { weights : Core.Hash Weights
  , architecture : Core.Hash Architecture
  , tokenizer : Core.Hash Tokenizer.TokenizerSpec
  , vocab : Core.Hash Vocab
  , tool_format : Core.Hash Tool.ToolFormat
  , delimiters : Delimiters
  , test_vectors : Core.Hash TestVectors
  }

let defaultDelimiters : Delimiters =
  { think_start = Some "<think>"
  , think_end = Some "</think>"
  , tool_start = Some "<tool_call>"
  , tool_end = Some "</tool_call>"
  , code_fence = "```"
  }

in { Model, Delimiters, defaultDelimiters }
