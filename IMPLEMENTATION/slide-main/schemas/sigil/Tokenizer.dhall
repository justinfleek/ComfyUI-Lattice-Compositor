let Core = ./Core.dhall

let Normalizer = { _type : Text }
let PreTokenizer = { _type : Text }
let Algorithm = < BPE | Unigram | WordLevel | WordPiece | Identity >

let SpecialToken = { id : Natural, text : Text }

let SpecialTokens =
  { bos : SpecialToken
  , eos : SpecialToken
  , pad : Optional SpecialToken
  , unk : Optional SpecialToken
  }

let TokenizerSpec =
  { vocab : Core.Hash { _type : Text }
  , merges : Optional (Core.Hash { _type : Text })
  , normalization : List Normalizer
  , pre_tokenization : PreTokenizer
  , algorithm : Algorithm
  , special_tokens : SpecialTokens
  , test_vectors : Core.Hash { _type : Text }
  }

in { TokenizerSpec, Algorithm, SpecialTokens, SpecialToken, Normalizer, PreTokenizer }
