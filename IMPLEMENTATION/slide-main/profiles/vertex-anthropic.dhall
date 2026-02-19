let P = ./prelude.dhall

let region = env:REGION as Text ? "us-east5"
let project = env:PROJECT_ID as Text ? "straylight-486401"
let model = "claude-opus-4-5@20251101"

-- Full endpoint construction
let endpoint = "https://${region}-aiplatform.googleapis.com/v1/projects/${project}/locations/${region}/publishers/anthropic/models/${model}:streamRawPredict"

in  { provider =
        { providerType = P.Provider.ProviderType.Vertex
        , endpoint = endpoint
        , auth = P.Provider.AuthScheme.Bearer
        , model_override = Some "vertex-2023-10-16" -- Used as anthropic_version in payload
        , timeout_secs = 600
        }
    , model = P.mkModel "0000000000000000000000000000000000000000000000000000000000000000" -- dummy hash
    , tokenizer_path = "identity"
    , hot_table_path = None Text
    }
