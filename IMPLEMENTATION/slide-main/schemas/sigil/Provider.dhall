let Core = ./Core.dhall

let AuthScheme = < ApiKey | Bearer | None | ApiKeyFile : Text >
let ProviderType = < OpenAI | Baseten | Vertex >

let Provider =
  { providerType : ProviderType
  , endpoint : Text
  , auth : AuthScheme
  , model_override : Optional Text
  , timeout_secs : Natural
  }

in { Provider, AuthScheme, ProviderType }
