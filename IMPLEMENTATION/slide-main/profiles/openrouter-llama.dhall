let P = ./prelude.dhall

in  { provider =
        { providerType = P.Provider.ProviderType.OpenAI
        , endpoint = "https://openrouter.ai/api/v1/chat/completions"
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "meta-llama/llama-3.1-70b-instruct"
        , timeout_secs = 300
        }
    , model = P.mkModel "e134af98b985517b4f068e3755ae90d4e9cd2d45d328325dc503f1c6b2d06cc7"
    , tokenizer_path = "tokenizers/llama-3-8b-Instruct/tokenizer.json"
    , hot_table_path = None Text
    }
