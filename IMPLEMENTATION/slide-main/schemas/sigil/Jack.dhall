let Provider = ./Provider.dhall
let Model = ./Model.dhall

let Jack =
  { provider : Provider.Provider
  , model : Model.Model
  , tokenizer_path : Text
  , hot_table_path : Optional Text
  }

in { Jack }
