let Core = ../schemas/sigil/Core.dhall
let Provider = ../schemas/sigil/Provider.dhall
let Model = ../schemas/sigil/Model.dhall
let Tokenizer = ../schemas/sigil/Tokenizer.dhall
let Jack = ../schemas/sigil/Jack.dhall

let sha256 = \(digest : Text) ->
      { algorithm = Core.HashAlgorithm.SHA256, digest = digest }

let dummyHash = sha256 "0000000000000000000000000000000000000000000000000000000000000000"

let mkModel = \(tokenizerHash : Text) ->
      { weights = dummyHash
      , architecture = dummyHash
      , tokenizer = sha256 tokenizerHash
      , vocab = dummyHash
      , tool_format = dummyHash
      , delimiters = Model.defaultDelimiters
      , test_vectors = dummyHash
      }

-- Helper to make providers with defaults
let mkProvider = \(type : Provider.ProviderType) -> \(endpoint : Text) ->
      { providerType = type
      , endpoint = endpoint
      , auth = Provider.AuthScheme.None
      , model_override = None Text
      , timeout_secs = 600
      }

let identitySpec : Tokenizer.TokenizerSpec =
  { vocab = dummyHash
  , merges = None (Core.Hash { _type : Text })
  , normalization = [] : List Tokenizer.Normalizer
  , pre_tokenization = { _type = "Identity" }
  , algorithm = Tokenizer.Algorithm.Identity
  , special_tokens =
      { bos = { id = 0, text = "" }
      , eos = { id = 0, text = "" }
      , pad = None Tokenizer.SpecialToken
      , unk = None Tokenizer.SpecialToken
      }
  , test_vectors = dummyHash
  }

in  { Core, Provider, Model, Jack, Tokenizer, sha256, mkModel, identitySpec, mkProvider }

