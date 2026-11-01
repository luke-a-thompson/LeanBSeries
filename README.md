# LeanBSeries

[![CI](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0--rc2-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Butcher series and Runge–Kutta order theory in Lean 4.

The cosine EES family is formalised for every odd antisymmetric order `m >= 3`.
The library proves exact classical order two, exact antisymmetric order `m`,
Williamson 2N storage, and the minimum stage count `(m + 1) / 2`.

The all-order Williamson transfer theorem is
[`BSeries.WilliamsonOrderTransfer`](BSeries/LieButcher/WilliamsonOrderTransfer.lean).
It proves that classical order `p` implies order `p` of the exponential lift,
for every finite stage count and every order, allowing zero coefficients.
The proof constructs homogeneous moment polynomials using area closure,
identifies them with the existing exponential-character recursion, and checks
their exact-flow specialization. It uses only the standard Lean axioms.

## Building

Requires the sibling repository
[LeanRoughPaths](https://github.com/daniil-shmelev/LeanRoughPaths)
(rooted trees and their Hopf algebras) checked out next to this one:

```
git clone https://github.com/daniil-shmelev/LeanRoughPaths lean-rough-paths
git clone https://github.com/daniil-shmelev/LeanBSeries    lean-b-series
git -C lean-rough-paths checkout 15ecc0414ae805b1ae57f05c8be170bd68361d19
git -C lean-rough-paths apply ../lean-b-series/patches/lean-rough-paths-lean-4.36.patch
cd lean-b-series
lake exe cache get
lake build
```

The small dependency patch makes six induction patterns independent of the
case-name change in Lean 4.36. CI uses the same dependency revision and patch.
