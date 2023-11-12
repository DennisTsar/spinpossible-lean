import Lake
open Lake DSL

def args := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DrelaxedAutoImplicit=false" -- helps avoid typo traps
]

package «spinpossible» {
  moreServerArgs := args
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Spinpossible» {
  moreLeanArgs := args
}
