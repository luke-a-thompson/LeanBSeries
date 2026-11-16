/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.LieButcher.WilliamsonOrderTransfer
import BSeries.Numerics.EES27

/-!
# Lie–Butcher order theorems for CF-EES(2,5;x) and CF-EES(2,7;x)

The order theorems of arXiv:2509.20599, Theorems E.1 and E.2, for the
commutator-free lifts of the parametric `EES` families.

Forward order two is an instance of `williamson_order_transfer`: both
families are Williamson 2N schemes of classical order two. The remaining
statements are verified **at the generic parameter**: over the computable
fields `CRatFunc ℚ` and `Qsqrt2` the antisymmetric order conditions
become identities checked by `native_decide` through the memoised
evaluator `CommutatorFreeMethod.fastMethodChar`.

The symbolic character values are cross-validated against Table 6 of
arXiv:2509.20599: e.g. on the planar cherry the `CF-EES(2,5;x)`
character equals `(2x-5)/(32(x-1))` as a rational function.

This file is a leaf module so that the native evaluations never block
edits to the general theory.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

open LowStorage CRatFunc CommutatorFreeMethod

/-! ### CF-EES(2,5;x): Theorem E.1 -/

/-- **`CF-EES(2,5;x)` has order two for every admissible parameter**
(arXiv:2509.20599, Theorem E.1(1)), on all ordered forests and over any
field of characteristic zero. -/
theorem hasOrder_two_cfEES25 {K : Type*} [Field K] [CharZero K] {x : K}
    (hx1 : x ≠ 1) (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) :
    (ees25LowStorage x).toCommutatorFree.HasOrder 2 :=
  williamson_order_transfer _ (by
    rw [toRK_ees25LowStorage hx1 hx2 hx3 two_ne_zero]
    exact hasOrder_two_ees25 hx1 hx2 hx3 two_ne_zero)

/-- The lift of the materialised generic `EES(2,5;X)` data (top-level
constant: evaluated once per process). -/
def cfEES25X : CommutatorFreeMethod (Fin 3) (CRatFunc ℚ) :=
  (ees25LowStorage (X : CRatFunc ℚ)).materialize.toCommutatorFree

set_option maxHeartbeats 2000000 in
/-- All decidable checks in one `native_decide` (each invocation compiles
the full closure natively, so they are consolidated). -/
private theorem cfEES25_checks :
    ((X : CRatFunc ℚ) ≠ 1 ∧ 2 * (X : CRatFunc ℚ) ≠ 1 ∧
      2 * (X : CRatFunc ℚ) ≠ -1) ∧
    (fastMethodChar cfEES25X [PTree.cherry] =
        (2 * X - 5) / (32 * (X - 1)) ∧
      fastMethodChar cfEES25X [PTree.chain3] = 1 / 8) ∧
    (∀ τ ∈ (List.range 6).flatMap PTree.treesOfOrder,
      LSSeries.symmetricDefect (fastMethodChar cfEES25X) [τ] = 0) ∧
    LSSeries.symmetricDefect (fastMethodChar cfEES25X)
      [PTree.tallTree 5] ≠ 0 := by
  native_decide

private theorem fast25 :
    (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.methodChar =
      fastMethodChar cfEES25X := by
  rw [cfEES25X, LowStorage.materialize_eq, fastMethodChar_eq]

/-- Cross-validation against arXiv:2509.20599, Table 6, **as an identity
of rational functions**: on the planar cherry the `CF-EES(2,5;x)`
character equals `(2x-5)/(32(x-1))`. -/
theorem methodChar_cfEES25_cherry_generic :
    (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.methodChar [PTree.cherry] =
      (2 * X - 5) / (32 * (X - 1)) := by
  rw [fast25]
  exact cfEES25_checks.2.1.1

/-- Cross-validation against arXiv:2509.20599, Table 6: on the
three-chain the character equals `1/8`, independently of the
parameter. -/
theorem methodChar_cfEES25_chain3_generic :
    (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.methodChar [PTree.chain3] =
      1 / 8 := by
  rw [fast25]
  exact cfEES25_checks.2.1.2

/-- `CF-EES(2,5;X)` has order two at the generic parameter. -/
theorem hasOrder_two_cfEES25_generic :
    (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.HasOrder 2 :=
  hasOrder_two_cfEES25 cfEES25_checks.1.1 cfEES25_checks.1.2.1
    cfEES25_checks.1.2.2

/-- `CF-EES(2,5;X)` does not have order three: on the three-chain its
character is `1/8`, and the exact flow has `1/6`. -/
theorem not_hasOrder_three_cfEES25_generic :
    ¬ (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.HasOrder 3 := by
  intro h
  have h3 := h [PTree.chain3] (by decide)
  rw [methodChar_cfEES25_chain3_generic] at h3
  norm_num [OrderedExpansion.exactCoeff, OrderedExpansion.forestDenominator,
    OrderedExpansion.treeDenominator, PTree.chain3, PTree.chain2, PTree.bullet,
    PTree.order, PTree.orderList] at h3

/-- **`CF-EES(2,5;X)` has antisymmetric order five at the generic
parameter** (arXiv:2509.20599, Theorem E.1(2)): the symmetric defect of
its LB character vanishes on all planar trees of order at most five, as
identities of rational functions in the parameter. -/
theorem hasPlanarAntisymOrder_five_cfEES25_generic :
    LSSeries.HasPlanarAntisymOrder
      (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.methodChar 5 := by
  rw [fast25]
  intro τ hτ
  have hmem : τ ∈ (List.range 6).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order τ, ?_, PTree.mem_treesOfOrder τ⟩
    exact List.mem_range.2 (by omega)
  exact cfEES25_checks.2.2.1 τ hmem

/-- `CF-EES(2,5;X)` does not have antisymmetric order six: the six-chain
is a witness at the generic parameter. -/
theorem not_hasPlanarAntisymOrder_six_cfEES25_generic :
    ¬ LSSeries.HasPlanarAntisymOrder
      (ees25LowStorage (X : CRatFunc ℚ)).toCommutatorFree.methodChar 6 := by
  rw [fast25]
  intro h
  exact cfEES25_checks.2.2.2
    (h (PTree.tallTree 5) (by rw [PTree.order_tallTree]))

/-! ### CF-EES(2,7;(2-√2)/4): Theorem E.2 at the representative -/

/-- **`CF-EES(2,7;(2-√2)/4)` has order two** (arXiv:2509.20599,
Theorem E.2), on all ordered forests. -/
theorem hasOrder_two_cfEES27 :
    (ees27LowStorage Qsqrt2.sqrt2 x27).toCommutatorFree.HasOrder 2 :=
  williamson_order_transfer _ (by
    rw [← LowStorage.materialize_eq (ees27LowStorage Qsqrt2.sqrt2 x27)]
    exact toRK_ees27rLowStorage ▸ hasOrder_two_ees27r)

/-- The lift of the materialised representative data. -/
def cfEES27r : CommutatorFreeMethod (Fin 4) Qsqrt2 :=
  ees27rLowStorage.toCommutatorFree

set_option maxHeartbeats 2000000 in
/-- All decidable checks in one `native_decide`. -/
private theorem cfEES27_checks :
    fastMethodChar cfEES27r [PTree.cherry] ≠
      OrderedExpansion.exactCoeff [PTree.cherry] ∧
    (∀ τ ∈ (List.range 8).flatMap PTree.treesOfOrder,
      LSSeries.symmetricDefect (fastMethodChar cfEES27r) [τ] = 0) ∧
    LSSeries.symmetricDefect (fastMethodChar cfEES27r)
      [PTree.tallTree 7] ≠ 0 := by
  native_decide

private theorem fast27 :
    (ees27LowStorage Qsqrt2.sqrt2 x27).toCommutatorFree.methodChar =
      fastMethodChar cfEES27r := by
  rw [cfEES27r, ees27rLowStorage, LowStorage.materialize_eq, fastMethodChar_eq]

/-- `CF-EES(2,7;(2-√2)/4)` does not have order three (cherry witness). -/
theorem not_hasOrder_three_cfEES27 :
    ¬ (ees27LowStorage Qsqrt2.sqrt2 x27).toCommutatorFree.HasOrder 3 := by
  intro h
  have h3 := h [PTree.cherry] (by decide)
  rw [fast27] at h3
  exact cfEES27_checks.1 h3

/-- **`CF-EES(2,7;(2-√2)/4)` has antisymmetric order seven**
(arXiv:2509.20599, Theorem E.2): the symmetric defect of its LB
character vanishes on all `197` planar trees of order at most seven. -/
theorem hasPlanarAntisymOrder_seven_cfEES27 :
    LSSeries.HasPlanarAntisymOrder
      (ees27LowStorage Qsqrt2.sqrt2 x27).toCommutatorFree.methodChar 7 := by
  rw [fast27]
  intro τ hτ
  have hmem : τ ∈ (List.range 8).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order τ, ?_, PTree.mem_treesOfOrder τ⟩
    exact List.mem_range.2 (by omega)
  exact cfEES27_checks.2.1 τ hmem

/-- `CF-EES(2,7;(2-√2)/4)` does not have antisymmetric order eight. -/
theorem not_hasPlanarAntisymOrder_eight_cfEES27 :
    ¬ LSSeries.HasPlanarAntisymOrder
      (ees27LowStorage Qsqrt2.sqrt2 x27).toCommutatorFree.methodChar 8 := by
  rw [fast27]
  intro h
  exact cfEES27_checks.2.2
    (h (PTree.tallTree 7) (by rw [PTree.order_tallTree]))

end RungeKutta

end BSeries
