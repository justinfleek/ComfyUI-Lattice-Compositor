let HashAlgorithm =
  < BLAKE3
  | SHA256
  | SHA3_256
  >

let Hash = \(T : Type) ->
  { algorithm : HashAlgorithm
  , digest : Text
  }

in
  { HashAlgorithm
  , Hash
  }
