/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.AlgebraicTridiagonal
import BSeries.Numerics.EESCosineOrder

/-!
# Williamson representation from maximal antisymmetric order

We use `ForestAlgebra.Character.HasAntisymOrder` for antisymmetric order and `LowStorage.toRK` for the tableau obtained by unrolling the Williamson recurrence. The abscissae `c = A𝟙` are already given by `RungeKutta.abscissa`.

Indices in `Fin s` are zero-based: `LowStorage.A i` and `LowStorage.B i` represent the coefficients `α_{i+1}` and `β_{i+1}` in the one-based recurrence `K_i = α_i K_{i-1} + h f(t_n + c_i h, Y_{i-1})`, `Y_i = Y_{i-1} + β_i K_i`, starting from `K_0 = 0` and `Y_0 = y_n`. Equality of the induced tableau with the original tableau expresses equality of all stages and of the final update `Y_s = y_{n+1}`.

Rooted-tree cancellation gives a bidiagonal polynomial operator. The full period and the quadratic node invariant separate the stage nodes. The node and subdiagonal recurrences give a quadratic operator identity; its dual relation forces the three-term recurrence directly in the stage-polynomial eigenbasis. The reverse-shift matrix records that recurrence and supplies the tableau row identities used by the shared Williamson reconstruction. Supporting lemmas live in `EESWilliamson/`, with general polynomial and matrix facts in `Algebra/` and reconstruction in `Williamson/`.
-/

namespace BSeries.RungeKutta

open scoped BigOperators

noncomputable section

local instance williamsonInvertibleTwo : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- A consistent real explicit `s`-stage tableau with `s ≥ 2` and antisymmetric order at least `2s - 1` has nonzero final-weight/subdiagonal product and the Williamson representation with coefficients `LowStorage.ofSubdiagonal`. Every `β_i`, hence every denominator in the formulas for `α_i`, is nonzero. No nonvanishing hypothesis is imposed on the earlier weights `b_j` with `j < s` in one-based notation. -/
theorem williamson_of_hasAntisymOrder {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk)
    (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    rk.b ⟨s - 1, by omega⟩ *
        (∏ i : Fin (s - 1),
          rk.A ⟨i.val + 1, by have := i.isLt; omega⟩
            ⟨i.val, by have := i.isLt; omega⟩) ≠ 0 ∧
      (LowStorage.ofSubdiagonal rk).toRK = rk ∧
      (∀ i, (LowStorage.ofSubdiagonal rk).B i ≠ 0) := by
  have hprod := subdiagonal_product_ne_zero_of_hasAntisymOrder (by omega) hexp hcons hanti
  have hB : ∀ i, (LowStorage.ofSubdiagonal rk).B i ≠ 0 := by
    intro i
    change rk.rowAfter i i ≠ 0
    unfold rowAfter
    by_cases hi : i.val + 1 < s
    · rw [dite_eq_left hi]
      exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).2)
        (⟨i.val, by omega⟩ : Fin (s - 1)) (Finset.mem_univ _)
    · rw [dite_eq_right hi]
      have heq : i = (⟨s - 1, by omega⟩ : Fin s) := by
        apply Fin.ext
        have := i.isLt
        dsimp
        omega
      rw [heq]
      exact (mul_ne_zero_iff.mp hprod).1
  refine ⟨hprod, toRK_ofSubdiagonal_eq_of_rowDifferenceCondition hexp hB ?_, hB⟩
  exact rowDifferenceCondition_of_reverseShift_tridiagonal hexp
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
    (forwardBackward_reverseShift_tridiagonal hs hexp hcons hanti)

/-- Every real minimal-stage `EES(2,m)` method is Williamson 2N, for odd `m ≥ 3`. Minimality is taken among all real tableaux in the same EES class. -/
theorem isWilliamson2N_of_minimalStage_isEES {s m : ℕ}
    {rk : RungeKutta (Fin s) ℝ} (hm : 3 ≤ m) (hodd : Odd m)
    (hees : IsEES rk 2 m)
    (hmin : ∀ {k : ℕ} (rk' : RungeKutta (Fin k) ℝ), IsEES rk' 2 m → s ≤ k) :
    IsWilliamson2N rk := by
  have hcons : weightBullet rk = 1 :=
    (hasOrder_one_iff_hasOrderOne rk).mp (hees.2.1.1.mono (by omega))
  have hlower := antisymOrder_lt_twice_stages hees.1 hcons hees.2.2.1
  have hupper := hmin (eesCosineForOrder m) (isEES_eesCosineForOrder hm hodd)
  obtain ⟨k, hk⟩ := hodd
  have hs : 2 ≤ s := by omega
  have horder : m = 2 * s - 1 := by omega
  have hanti := hees.2.2.1
  rw [horder] at hanti
  exact ⟨LowStorage.ofSubdiagonal rk,
    (williamson_of_hasAntisymOrder hs hees.1 hcons hanti).2.1⟩

end

end BSeries.RungeKutta
