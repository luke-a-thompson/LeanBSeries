import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-rough-paths» from git
  "https://github.com/luke-a-thompson/LeanRoughPaths" @
  "95f85b915352e0838d1da62538763622481a020a"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."
