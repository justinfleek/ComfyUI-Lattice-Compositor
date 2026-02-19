import Lake
open Lake DSL

package transpiler {}

require megaparsec from git "https://github.com/lurk-lab/Megaparsec.lean" @ "main"

lean_lib Transpiler {}

lean_exe transpiler {
  root := `Transpiler`
}
