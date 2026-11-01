# LeanBSeries

[![CI](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0--rc3-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Butcher series and Runge–Kutta order theory in Lean 4.

The cosine EES family is formalised for every odd antisymmetric order `m >= 3`.
The library proves exact classical order two, exact antisymmetric order `m`,
Williamson 2N storage, and the minimum stage count `(m + 1) / 2`.

The all-order Williamson transfer statement is
[`BSeries.WilliamsonOrderTransfer`](BSeries/LieButcher/WilliamsonOrderTransfer.lean).
It is currently an **unproved proposition**, not a theorem. The coefficient-path
area closure, its connection to `LowStorage.toRK`, and the elementary-column
grafting identity are proved in
[`AreaTableau.lean`](BSeries/Numerics/Williamson/AreaTableau.lean).
The remaining step is the homogeneous moment-polynomial reduction for arbitrary
ordered coefficients, including its exact-flow specialization.

## Building

Requires the sibling repository
[LeanRoughPaths](https://github.com/daniil-shmelev/LeanRoughPaths)
(rooted trees and their Hopf algebras) checked out next to this one:

```
git clone https://github.com/daniil-shmelev/LeanRoughPaths lean-rough-paths
git clone https://github.com/daniil-shmelev/LeanBSeries    lean-b-series
cd lean-b-series
lake exe cache get
lake build
```
