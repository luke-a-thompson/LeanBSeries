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
[`BSeries.williamson_order_transfer`](BSeries/LieButcher/WilliamsonOrderTransfer.lean):

```lean
theorem williamson_order_transfer {s p : ℕ} (ls : RungeKutta.LowStorage s ℝ)
    (hRK : RungeKutta.HasOrder ls.toRK p) :
    CommutatorFreeMethod.HasOrder ls.toCommutatorFree p
```

`CommutatorFreeMethod.HasOrder`
([`CommutatorFreeCharacter.lean`](BSeries/LieButcher/CommutatorFreeCharacter.lean))
is defined for any commutator-free method, with no reference to a Butcher
tableau. The Lie–Butcher coefficients of a composition of exponentials are the
signature of its piecewise-linear coefficient path, stage generators are
expanded recursively through the stage points, and order `p` means agreement
with the exact flow on every ordered forest of degree at most `p`. Classical
order does not imply it in general: a step with a single exponential never has
order three (`not_hasOrder_three_of_stepExps_singleton`).

The proof identifies the coefficients of the Bazavov lift with the
chronological recursion `LowStorage.flowChar`, constructs homogeneous moment
polynomials using the Williamson area closure, and checks their exact-flow
specialization. It holds for every stage count and order, allows zero
coefficients, and uses only the standard Lean axioms (checked in the file by
`#guard_msgs`).

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
