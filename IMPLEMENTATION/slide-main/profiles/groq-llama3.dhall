let P = ./prelude.dhall

in  { provider =
        { providerType = P.Provider.ProviderType.OpenAI
        , endpoint = "https://api.groq.com/openai/v1/chat/completions"
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "llama3-8b-8192"
        , timeout_secs = 300
        }
    , model = P.mkModel "e134af98b985517b4f068e3755ae90d4e9cd2d45d328325dc503f1c6b2d06cc7"
    , tokenizer_path = "tokenizers/llama-3-8b-Instruct/tokenizer.json"
    , hot_table_path = None Text
    }
