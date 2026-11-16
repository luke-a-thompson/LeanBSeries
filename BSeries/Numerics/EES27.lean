/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Algebra.Qsqrt2
import BSeries.Numerics.EES25
import BSeries.Numerics.FastWeight

/-!
# The EES(2,7;x) family

The four-stage `EES(2,7;x)` Runge–Kutta family (arXiv:2507.21006,
Section 8, positive `√2` branch), over any field `R` with a chosen
square root `s` of two. The Butcher tableau is

  `b = (x, (2-s)/2 - (1-s)x, (1-s)(x-1), (2-s)/2 - x)`

with the stage matrix recorded below; the concrete representatives at
`x = (2-√2)/4` and `x = (5-3√2)/14` of the paper arise by
specialisation.

The representative at `x = (5-3√2)/14` has checked exact orders two and
seven (`isEES_ees27r`) and Williamson 2N storage (`isWilliamson2N_ees27r`).
The cosine representative belongs to the general family in `EESCosineOrder`.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v

variable {R : Type v}

/-- The four-stage `EES(2,7;x)` family (arXiv:2507.21006, Section 8,
`+√2` branch), over a field with a distinguished square root `s` of two:
the stage matrix of the proposition, with
`α = (2x+s)/((2x-1)(1-s-2x))` and `β = 1/((2x-1)(1-s-2x)(2-s-2x))`. -/
def ees27 [Field R] (s x : R) : RungeKutta (Fin 4) R where
  A i j :=
    ![![0, 0, 0, 0],
      ![(-2 + s * (1 - 2 * x)) / (4 * (x - 1)), 0, 0, 0],
      ![((2 * x + s - 2) * (4 * x + s - 2) / (4 * s * (x - 1))) *
          ((2 * x + s) / ((2 * x - 1) * (1 - s - 2 * x))),
        ((-1 + s) / 2) * ((2 * x + s) / ((2 * x - 1) * (1 - s - 2 * x))),
        0, 0],
      ![((2 * x - s) * (-40 * x ^ 4 + (80 - 40 * s) * x ^ 3 -
            (88 - 60 * s) * x ^ 2 + (48 - 34 * s) * x + 7 * s - 10) /
          (4 * (x - 1) * (2 * x ^ 2 - 1))) *
          (1 / ((2 * x - 1) * (1 - s - 2 * x) * (2 - s - 2 * x))),
        (2 - s) * x * (x - 1) * (4 * x + s - 2) *
          (1 / ((2 * x - 1) * (1 - s - 2 * x) * (2 - s - 2 * x))),
        ((2 - s) * (2 * x - s) * (2 + s - 2 * x) * (x - 1) * (2 * x - 1)) /
          (4 * (2 * x ^ 2 - 1) * (2 * x ^ 2 - 4 * x + 1)),
        0]] i j
  b j :=
    ![x, (2 - s) / 2 - (1 - s) * x, (1 - s) * (x - 1),
      (2 - s) / 2 - x] j

/-- The family is explicit for all parameters: the strictly upper
triangle of the stage matrix consists of literal zeros. -/
theorem isExplicit_ees27 [Field R] (s x : R) : IsExplicit (ees27 s x) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hij (by decide)

/-- The Williamson coefficients of `EES(2,7;x)`, recovered from consecutive tableau rows. The shared constructor divides only by subdiagonal entries and the final weight. -/
def ees27LowStorage [Field R] (s x : R) : LowStorage 4 R :=
  LowStorage.ofSubdiagonal (ees27 s x)

/-! ### The representative parameter `x = (2-√2)/4`

Verifying the `EES(2,7;x)` order conditions symbolically in `x` is a
heavy rational-function computation over `ℚ(√2)(x)`; the machine-checked
verification below is at the numerically simple representative
`x = (2-√2)/4` of arXiv:2507.21006, Section 8, over the computable field
`ℚ(√2)`. (The three-stage `EES(2,5;x)` family *is* verified at the
generic parameter, in `BSeries.Numerics.EES25`.) -/

section Representative

/-- The representative parameter `(2-√2)/4`. -/
def x27 : Qsqrt2 := ⟨1/2, -1/4⟩

/-- The `EES(2,7; (2-√2)/4)` scheme, obtained from the family. -/
def ees27r : RungeKutta (Fin 4) Qsqrt2 :=
  ees27 Qsqrt2.sqrt2 x27

theorem isExplicit_ees27r : IsExplicit ees27r :=
  isExplicit_ees27 _ _

/-- The materialised composed tableau `ees27r ∘ ees27r` (top-level
constant: entries are evaluated once per process). -/
def ees27rComp : RungeKutta (Fin 8) Qsqrt2 :=
  materialize (reindex (finSumFinEquiv (m := 4) (n := 4)).symm
    (compose ees27r ees27r))

/-- The materialised composed tableau `ees27r* ∘ ees27r`. -/
def ees27rAdj : RungeKutta (Fin 8) Qsqrt2 :=
  materialize (reindex (finSumFinEquiv (m := 4) (n := 4)).symm
    (compose (adjointScheme ees27r) ees27r))

/-- The materialised low-storage data at the representative. -/
def ees27rLowStorage : LowStorage 4 Qsqrt2 :=
  (ees27LowStorage Qsqrt2.sqrt2 x27).materialize

set_option maxHeartbeats 2000000 in
/-- All decidable order checks in one `native_decide` (each invocation
compiles the full tableau closure natively, so they are consolidated). -/
private theorem ees27r_checks :
    (weight ees27r PTree.bullet = 1 ∧ weight ees27r PTree.chain2 * 2 = 1) ∧
    weight ees27r PTree.cherry * 3 ≠ 1 ∧
    (∀ t ∈ (List.range 8).flatMap PTree.treesOfOrder,
      fastWeight ees27rComp t = fastWeight ees27rAdj t) ∧
    (∀ i j, ees27rLowStorage.toRK.A i j = ees27r.A i j) ∧
    (∀ j, ees27rLowStorage.toRK.b j = ees27r.b j) := by
  native_decide

/-- `EES(2,7;(2-√2)/4)` has order two (machine-checked). -/
theorem hasOrder_two_ees27r : HasOrder ees27r 2 := by
  rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
  exact ⟨by simpa [HasOrderOne] using ees27r_checks.1.1,
    eq_inv_of_mul_eq_one_left ees27r_checks.1.2⟩

/-- `EES(2,7;(2-√2)/4)` does not have order three (cherry witness). -/
theorem not_hasOrder_three_ees27r : ¬ HasOrder ees27r 3 := by
  intro h
  have hval := ((hasOrder_three_iff_hasOrder_two_and_weight_chain3_and_cherry _).mp h).2.2
  refine ees27r_checks.2.1 ?_
  rw [hval]
  norm_num

/-- **`EES(2,7;(2-√2)/4)` has antisymmetric order seven**
(machine-checked composed-weight identities). -/
theorem hasAntisymOrder_seven_ees27r :
    ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series ees27r)) 7 := by
  rw [hasAntisymOrder_iff_weight_compose_eq]
  intro t ht
  have hmem : t ∈ (List.range 8).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order t, ?_, PTree.mem_treesOfOrder t⟩
    exact List.mem_range.2 (by have := PTree.order_pos t; omega)
  have h := ees27r_checks.2.2.1 t hmem
  rw [fastWeight_eq, fastWeight_eq, ees27rComp, ees27rAdj,
    materialize_eq, materialize_eq, weight_reindex, weight_reindex] at h
  exact h

/-- The four-stage bound excludes antisymmetric order eight for `EES(2,7;(2-√2)/4)`. -/
theorem not_hasAntisymOrder_eight_ees27r :
    ¬ ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series ees27r)) 8 :=
  not_hasAntisymOrder_twice_stages isExplicit_ees27r
    (hasOrder_two_ees27r.hasOrderOne (by norm_num))

/-- **`EES(2,7;(2-√2)/4)` is an `EES(2,7)` scheme** (arXiv:2507.21006,
Section 8): explicit, of order exactly two, with antisymmetric order
exactly seven. -/
theorem isEES_ees27r : IsEES ees27r 2 7 :=
  ⟨isExplicit_ees27r,
    ⟨hasOrder_two_ees27r, not_hasOrder_three_ees27r⟩,
    ⟨hasAntisymOrder_seven_ees27r, not_hasAntisymOrder_eight_ees27r⟩⟩

/-- The two-register coefficients induce the `EES(2,7;(2-√2)/4)` tableau. -/
theorem toRK_ees27rLowStorage : ees27rLowStorage.toRK = ees27r :=
  ext ees27r_checks.2.2.2.1 ees27r_checks.2.2.2.2

/-- **`EES(2,7;(2-√2)/4)` is Williamson 2N** (arXiv:2509.20599,
Proposition 3.1): the two-register coefficients read off the tableau
induce it back. -/
theorem isWilliamson2N_ees27r : IsWilliamson2N ees27r :=
  ⟨ees27rLowStorage, toRK_ees27rLowStorage⟩

end Representative

end RungeKutta

end BSeries
