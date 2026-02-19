let P = ./prelude.dhall

let region = env:REGION as Text ? "us-central1"
let project = env:PROJECT_ID as Text ? "my-project"
let endpoint = "https://${region}-aiplatform.googleapis.com/v1beta1/projects/${project}/locations/${region}/endpoints/openai/chat/completions"

in  { provider =
        { providerType = P.Provider.ProviderType.Baseten -- Vertex OpenAI compatibility
        , endpoint = endpoint
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "gemini-3-pro-preview"
        , timeout_secs = 600
        }
    , model = P.mkModel "c0382117ea329cdf097041132f6d735924b697924d6f6fc3945713e96ce87539"
    , tokenizer_path = "tokenizers/Qwen2.5-7B-Instruct/tokenizer.json"
    , hot_table_path = None Text
    }
