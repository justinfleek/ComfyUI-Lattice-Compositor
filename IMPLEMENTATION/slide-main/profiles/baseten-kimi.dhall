let P = ./prelude.dhall

-- Using the working endpoint from manual testing
let endpoint = "https://inference.baseten.co/v1/chat/completions"

in  { provider =
        { providerType = P.Provider.ProviderType.Baseten
        , endpoint = endpoint
        , auth = P.Provider.AuthScheme.ApiKey
        , model_override = Some "moonshotai/Kimi-K2.5"
        , timeout_secs = 600
        }
    , model = P.mkModel "c0382117ea329cdf097041132f6d735924b697924d6f6fc3945713e96ce87539"
    , tokenizer_path = "tokenizers/moonshotai/Kimi-K2.5/tokenizer.json"
    , hot_table_path = None Text
    }
