let RoleFormat =
  { prefix : Text
  , suffix : Text
  }

let SystemPosition = < Top | TopAndBottom | Anywhere >

let SequenceFormat =
  { bos : Bool
  , eos_after : Text
  , system_position : SystemPosition
  }

let ChatFormat =
  { roles : { system : RoleFormat, user : RoleFormat, assistant : RoleFormat }
  , turn_separator : Text
  , sequence : SequenceFormat
  }

in { ChatFormat, RoleFormat, SequenceFormat }
