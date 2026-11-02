import Lake
open Lake DSL

package «LeanBSeries» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-rough-paths» from git
  "https://github.com/luke-a-thompson/LeanRoughPaths" @
  "2402b9395fc33b51bc46ac795fb69f939258015d"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «BSeries» where
  srcDir := "."
