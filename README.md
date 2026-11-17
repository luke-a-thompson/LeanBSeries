# LeanBSeries

[![CI](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0--rc3-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Butcher series and Runge–Kutta order theory in Lean 4.

The cosine EES family is formalised for every odd antisymmetric order `m >= 3`.
The library proves exact classical order two, exact antisymmetric order `m`,
Williamson 2N storage, and the minimum stage count `(m + 1) / 2`.

The all-order Williamson transfer theorem is
[`BSeries.williamson_order_transfer`](BSeries/LieButcher/WilliamsonOrderTransfer.lean):

```lean
theorem williamson_order_transfer {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    (ls : RungeKutta.LowStorage s K) (hRK : RungeKutta.HasOrder ls.toRK p) :
    CommutatorFreeMethod.HasOrder ls.toCommutatorFree p
```

`CommutatorFreeMethod.HasOrder`
([`CommutatorFreeSeries.lean`](BSeries/LieButcher/CommutatorFreeSeries.lean))
is defined for any commutator-free method, with no reference to a Butcher
tableau. The Lie–Butcher coefficients of a composition of exponentials are the
signature of its piecewise-linear coefficient path, stage generators are
expanded recursively through the stage points, and order `p` means agreement
with the exact flow on every ordered forest of degree at most `p`. Classical
order does not imply it in general: a step with a single exponential never has
order three (`not_hasOrder_three_of_stepExps_singleton`).

The proof shows that the moment polynomials of a forest, built from the
Williamson area closure, satisfy Chen's identity along the coefficient path,
so they are the coefficients of the Bazavov lift, and then checks their
exact-flow specialization. It holds for every stage count and order, over any
field of characteristic zero, allows zero coefficients, and uses only the
standard Lean axioms (checked in the file by `#guard_msgs`).

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
