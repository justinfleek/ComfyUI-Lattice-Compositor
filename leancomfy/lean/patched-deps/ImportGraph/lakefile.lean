import Lake
open Lake DSL

package «importGraph»

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.27.0-rc1"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

lean_lib «ImportGraph»
