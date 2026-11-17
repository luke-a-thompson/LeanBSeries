import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-rough-paths» from git
  "https://github.com/luke-a-thompson/LeanRoughPaths" @
  "de0457445b990854786e56ecd2698266f85be6cd"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."
