import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-rough-paths» from git
  "https://github.com/luke-a-thompson/LeanRoughPaths" @
  "5ef894a56c4aa11a058d6e039ab53873c4c2e17e"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."
