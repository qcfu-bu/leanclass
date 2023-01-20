import Lake
open Lake DSL


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "d1e6d8643531bd36f7c7bb612413decb7cb07ede"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "0d3734d33d53e1a34b98cb66edd63816fc69bc3f"

package «brown-cs22» {
  -- add package configuration options here
}

lean_lib BrownCs22 {
  -- add library configuration options here
}

@[default_target]
lean_exe «brown-cs22» {
  root := `Main
}
