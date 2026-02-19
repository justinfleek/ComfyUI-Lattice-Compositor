let Core = ./schemas/sigil/Core.dhall
let Jack = ./schemas/sigil/Jack.dhall
let Provider = ./schemas/sigil/Provider.dhall
let Model = ./schemas/sigil/Model.dhall
let Tokenizer = ./schemas/sigil/Tokenizer.dhall
let Tool = ./schemas/sigil/Tool.dhall

-- Define Qwen 2.5 72B Instruct Model Spec
let qwen_model =
      { weights = { algorithm = Core.HashAlgorithm.SHA256, digest = "TODO" }
      , architecture = { algorithm = Core.HashAlgorithm.SHA256, digest = "TODO" }
      , tokenizer = 
          { algorithm = Core.HashAlgorithm.SHA256
          -- The hash we just calculated
          , digest = "c0382117ea329cdf097041132f6d735924b697924d6f6fc3945713e96ce87539" 
          }
      , vocab = { algorithm = Core.HashAlgorithm.SHA256, digest = "TODO" }
      , tool_format = { algorithm = Core.HashAlgorithm.SHA256, digest = "TODO" }
      , test_vectors = { algorithm = Core.HashAlgorithm.SHA256, digest = "TODO" }
      }

-- Define Baseten Provider
let baseten_provider =
      { endpoint = "https://inference.baseten.co/v1/chat/completions"
      , auth = Provider.AuthScheme.ApiKey
      , model_override = None Text
      , timeout_secs = 300
      }

in
  { provider = baseten_provider
  , model = qwen_model
  , tokenizer_path = "./tokenizer.json"
  , hot_table_path = None Text
  }
