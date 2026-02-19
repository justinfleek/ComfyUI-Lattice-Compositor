// PureScript FFI bindings for Straylight.Nix.Value
// These call the same C functions used by the Haskell implementation

"use strict";

// Value is an opaque handle (32-bit integer)
exports.getValueId = function(v) {
  return v;
};

exports.getType = function(v) {
  // Call C function: c_get_type(ValueId) -> Word32
  // PureScript WASM FFI will handle this
  return v; // Placeholder - actual FFI needed
};

exports.panic = function(msg) {
  return function() {
    // Call C function: c_panic(char*, size_t)
    throw new Error("Nix panic: " + msg);
  };
};

exports.warn = function(msg) {
  return function() {
    // Call C function: c_warn(char*, size_t)
    console.warn("Nix warning: " + msg);
  };
};

exports.mkInt = function(n) {
  return function() {
    // Call C function: c_make_int(Int64) -> ValueId
    return n; // Placeholder
  };
};

exports.mkFloat = function(f) {
  return function() {
    // Call C function: c_make_float(Double) -> ValueId
    return f; // Placeholder
  };
};

exports.mkString = function(s) {
  return function() {
    // Call C function: c_make_string(char*, size_t) -> ValueId
    return s; // Placeholder
  };
};

exports.mkBool = function(b) {
  return function() {
    // Call C function: c_make_bool(int) -> ValueId
    return b ? 1 : 0; // Placeholder
  };
};

exports.mkNull = function() {
  // Call C function: c_make_null() -> ValueId
  return null; // Placeholder
};

exports.mkPath = function(p) {
  return function() {
    // Call C function: c_make_path(char*, size_t) -> ValueId
    return p; // Placeholder
  };
};

exports.mkList = function(vs) {
  return function() {
    // Call C function: c_make_list(ValueId*, size_t) -> ValueId
    return vs; // Placeholder
  };
};

exports.mkAttrs = function(attrs) {
  return function() {
    // Call C function: c_make_attrset(Entry*, size_t) -> ValueId
    // Entry format: { namePtr: u32, nameLen: u32, value: u32 }
    return attrs; // Placeholder
  };
};

exports.getInt = function(v) {
  return function() {
    // Call C function: c_get_int(ValueId) -> Int64
    return v; // Placeholder
  };
};

exports.getFloat = function(v) {
  return function() {
    // Call C function: c_get_float(ValueId) -> Double
    return v; // Placeholder
  };
};

exports.getString = function(v) {
  return function() {
    // Call C function: c_copy_string(ValueId, char*, size_t) -> size_t
    return String(v); // Placeholder
  };
};

exports.getBool = function(v) {
  return function() {
    // Call C function: c_get_bool(ValueId) -> int
    return v !== 0; // Placeholder
  };
};

exports.getPath = function(v) {
  return function() {
    // Call C function: c_copy_path(ValueId, char*, size_t) -> size_t
    return String(v); // Placeholder
  };
};

exports.getList = function(v) {
  return function() {
    // Call C function: c_copy_list(ValueId, ValueId*, size_t) -> size_t
    return []; // Placeholder
  };
};

exports.getAttrs = function(v) {
  return function() {
    // Call C function: c_copy_attrset(ValueId, Entry*, size_t) -> size_t
    return []; // Placeholder
  };
};

exports.getAttrsLen = function(v) {
  return function() {
    // Call C function: c_get_attrs_len(ValueId) -> size_t
    return 0; // Placeholder
  };
};

exports.getAttr = function(v) {
  return function(name) {
    return function() {
      // Call C function: c_get_attr(ValueId, char*, size_t) -> Maybe ValueId
      return null; // Placeholder
    };
  };
};

exports.hasAttr = function(v) {
  return function(name) {
    return function() {
      // Call C function: c_has_attr(ValueId, char*, size_t) -> int
      return false; // Placeholder
    };
  };
};

exports.call = function(f) {
  return function(arg) {
    return function() {
      // Call C function: c_call_function(ValueId, ValueId) -> ValueId
      return arg; // Placeholder
    };
  };
};

exports.call1 = function(f) {
  return function(arg) {
    return function() {
      // Call C function: c_call_function(ValueId, ValueId) -> ValueId
      return arg; // Placeholder
    };
  };
};

exports.call2 = function(f) {
  return function(arg1) {
    return function(arg2) {
      return function() {
        // Call C function: c_call_function(ValueId, ValueId) -> ValueId
        // (needs currying for two args)
        return arg1; // Placeholder
      };
    };
  };
};

exports.nixWasmInit = function() {
  // Call C function: nix_wasm_init_v1()
  // This initializes the WASM plugin
};
