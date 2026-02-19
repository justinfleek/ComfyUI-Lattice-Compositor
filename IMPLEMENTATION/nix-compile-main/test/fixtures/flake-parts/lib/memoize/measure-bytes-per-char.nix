# Run with:
#                                                      // nix // show // stats
#                                                      // nix // show // stats

{ control ? false, size ? 10 }:

let
  lib = import <nixpkgs/lib>;
  inherit (import ./memoize.nix { inherit lib; }) memoizeStr;

  # Create a string of the specified size
  key = lib.concatStrings (lib.genList (i: "a") size);

  # Memoized identity function
  memoId = memoizeStr (x: x);

  # Prime the trie with a minimal query to force its construction
  prime = memoId "";

in
if control
then builtins.seq prime key  # Return key after priming
else builtins.seq prime (memoId key)  # Pass through memoization after priming
