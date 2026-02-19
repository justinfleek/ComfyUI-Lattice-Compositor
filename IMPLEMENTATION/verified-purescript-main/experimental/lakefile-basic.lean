import Lake
open Lake DSL

package transpiler {}

lean_lib Transpiler {}

lean_exe transpiler {
  root := `Transpiler`
}
