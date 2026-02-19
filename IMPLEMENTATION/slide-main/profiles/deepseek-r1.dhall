let P = ./prelude.dhall

in  { provider =
        { providerType = P.Provider.ProviderType.OpenAI
        , endpoint = "https://api.deepseek.com/chat/completions"
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "deepseek-reasoner"
        , timeout_secs = 600
        }
    , model = P.mkModel "621ac2e32d0dba658404412318818aaa8ce8cda492e59830109d8da6b517fb41"
    , tokenizer_path = "tokenizers/DeepSeek-V3/tokenizer.json"
    , hot_table_path = None Text
    }
