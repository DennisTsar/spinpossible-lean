import Lake
open Lake DSL

package spinpossible where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩ -- helps avoid typo traps
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "main"

@[default_target]
lean_lib Spinpossible where
  globs := #[.submodules `Spinpossible]
