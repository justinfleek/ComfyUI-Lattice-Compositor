let P = ./prelude.dhall

in  { provider =
        { providerType = P.Provider.ProviderType.OpenAI
        , endpoint = "https://openrouter.ai/api/v1/chat/completions"
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "moonshotai/kimi-k2.5"
        , timeout_secs = 600
        }
    , model = P.mkModel "0000000000000000000000000000000000000000000000000000000000000000"
    , tokenizer_path = "identity"
    , hot_table_path = None Text
    }
