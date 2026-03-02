# Helper function to resolve output paths
# Handles both default ($out) and named outputs ($dev, $lib, etc.)
resolveOutPath = outputName: path:
  if outputName == "out" then
    "$out/${path}"
  else
    "$${${outputName}}/${path}";

# Extract output name and path from a path string
# Format: "dev:include/foo.h" → { output = "dev"; path = "include/foo.h"; }
# Format: "include/foo.h" → { output = "out"; path = "include/foo.h"; }
parseOutPath = pathStr:
  let
    parts = lib.splitString ":" pathStr;
  in
  if lib.length parts == 2 then
    {
      output = lib.elemAt parts 0;
      path = lib.elemAt parts 1;
    }
  else
    {
      output = "out";
      path = pathStr;
    };

# Resolve a path string to the actual output path
# Handles "dev:include/foo.h" → ${dev}/include/foo.h
# Handles "include/foo.h" → $out/include/foo.h
resolvePath = pathStr:
  let
    parsed = parseOutPath pathStr;
  in
  resolveOutPath parsed.output parsed.path;
