# LeanBSeries

[![CI](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0--rc3-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Butcher series and Runge–Kutta order theory in Lean 4.

The cosine EES family is formalised for every odd antisymmetric order `m >= 3`.
The library proves exact classical order two, exact antisymmetric order `m`,
Williamson 2N storage, and the minimum stage count `(m + 1) / 2`.

## Building

Lake fetches the pinned
[LeanRoughPaths fork](https://github.com/luke-a-thompson/LeanRoughPaths/tree/williamson-order-transfer)
(rooted trees and their Hopf algebras, plus the derivation area reduction
used by the Williamson proof):

```
git clone https://github.com/luke-a-thompson/LeanBSeries lean-b-series
cd lean-b-series
lake exe cache get
lake build
```
