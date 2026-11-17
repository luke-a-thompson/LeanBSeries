import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-rough-paths» from git
  "https://github.com/luke-a-thompson/LeanRoughPaths" @
  "da46867c90ada5e45a2774bad460e9003a1fc44c"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."
