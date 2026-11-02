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

Lake fetches the pinned [LeanRoughPaths fork](https://github.com/luke-a-thompson/LeanRoughPaths/tree/area-generation), including homogeneous area generation and the shared polynomial reduction.

```sh
git clone https://github.com/luke-a-thompson/LeanBSeries lean-b-series
cd lean-b-series
lake exe cache get
lake build
```

The Williamson proof uses `HopfAlgebras.Word.AreaReduction.diff_primitive`; its
rooted-tree grading and method-specific path identities remain in this repository.
Moment polynomials use Mathlib `Finsupp` and `LinearMap`. The coefficient path
is defined directly from the finite tableau rows in `AreaTableau.lean`.
The general word theorem is `HopfAlgebras.Word.Polynomial.word_generated` in the fork.
