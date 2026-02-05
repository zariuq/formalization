import Lake
open Lake DSL

package «catLogic» where
  srcDir := "src"
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «CategoricalLogic» where
  globs := #[
    .submodules `categoryTheory,
    .submodules `deduction,
    .submodules `semantics,
    `generalTactics
  ]
