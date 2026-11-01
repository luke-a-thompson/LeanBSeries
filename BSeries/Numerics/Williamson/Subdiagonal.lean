/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson.Reconstruction

/-!
# Reconstruction from subdiagonal entries

`LowStorage.ofSubdiagonal` recovers the register coefficients from consecutive tableau rows. Nonzero subdiagonal entries and final weight suffice when `RowDifferenceCondition` holds; earlier output weights may vanish. This complements `LowStorage.ofTableau`, which divides by output weights instead.
-/

namespace BSeries.RungeKutta

open scoped BigOperators

variable {R : Type*} {s : ℕ}

/-- Consecutive row differences are proportional on earlier columns; the output is the row following the final stage. -/
def RowDifferenceCondition [Field R] (rk : RungeKutta (Fin s) R) : Prop :=
  ∀ (i : Fin s) (_hi : 0 < i.val) (j : Fin s), j < i →
    let p : Fin s := ⟨i.val - 1, by have := i.isLt; omega⟩
    rk.rowDifference i j = (rk.rowDifference i p / rk.A i p) * rk.rowDifference p j

namespace LowStorage

/-- The proposed Williamson coefficients, reconstructed from the subdiagonal and the final weight. In one-based notation, `β_i = a_{i+1,i}` for `i < s`, `β_s = b_s`, `α_1 = 0`, `α_i = (a_{i+1,i-1} - a_{i,i-1}) / a_{i+1,i}` for `1 < i < s`, and `α_s = (b_{s-1} - a_{s,s-1}) / b_s`. -/
def ofSubdiagonal [Field R] (rk : RungeKutta (Fin s) R) : LowStorage s R where
  B i := rk.rowAfter i i
  A i :=
    if 0 < i.val then
      let j : Fin s := ⟨i.val - 1, by have := i.isLt; omega⟩
      rk.rowDifference i j / rk.rowAfter i i
    else 0

variable [Field R]

theorem ofSubdiagonal_B_succ (rk : RungeKutta (Fin s) R)
    {i k : Fin s} (hk : i.val + 1 = k.val) :
    (ofSubdiagonal rk).B i = rk.A k i :=
  rowAfter_succ rk hk i

theorem ofSubdiagonal_B_last {n : ℕ} (rk : RungeKutta (Fin (n + 1)) R) :
    (ofSubdiagonal rk).B (Fin.last n) = rk.b (Fin.last n) :=
  rowAfter_last rk (Fin.last n)

theorem ofSubdiagonal_A_succ (rk : RungeKutta (Fin s) R)
    {i k : Fin s} (hk : i.val + 1 = k.val) :
    (ofSubdiagonal rk).A k = rk.rowDifference k i / (ofSubdiagonal rk).B k := by
  have hpos : 0 < k.val := by omega
  simp only [ofSubdiagonal, ite_eq_left hpos]
  have heq : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin s) = i :=
    Fin.ext (by change k.val - 1 = i.val; omega)
  rw [heq]

/-- The unrolled weights satisfy the register recurrence in the stage index. -/
theorem beta_succ_left (ls : LowStorage s R) {i k j : Fin s}
    (hk : i.val + 1 = k.val) (hji : j ≤ i) (hB : ls.B i ≠ 0) :
    ls.beta k j = (ls.B k * ls.A k / ls.B i) * ls.beta i j := by
  have hjk : j ≤ k := by simp only [Fin.le_def] at *; omega
  have hp : ls.prodA j.val k.val = ls.prodA j.val i.val * ls.A k := by
    simp only [prodA, ← hk]
    rw [Finset.prod_Ico_succ_top (by simp only [Fin.le_def] at hji; omega),
      dite_eq_left (show i.val + 1 < s from hk ▸ k.isLt)]
    congr 2
    exact Fin.ext hk
  rw [beta, beta, ite_eq_left hjk, ite_eq_left hji, hp]
  field_simp

end LowStorage

variable [Field R]

/-- Nonzero subdiagonal entries and final weight suffice for reconstruction from the row identities. -/
theorem toRK_ofSubdiagonal_eq_of_rowDifferenceCondition
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (hB : ∀ i, (LowStorage.ofSubdiagonal rk).B i ≠ 0)
    (hrows : RowDifferenceCondition rk) :
    (LowStorage.ofSubdiagonal rk).toRK = rk := by
  let ls := LowStorage.ofSubdiagonal rk
  have hdiff (n : ℕ) : ∀ (i : Fin s), i.val = n → ∀ j,
      rk.rowDifference i j = ls.beta i j := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hin j
      rcases lt_trichotomy j i with hji | rfl | hij
      · have hip : 0 < i.val := by simp only [Fin.lt_def] at hji; omega
        let p : Fin s := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hp : p.val + 1 = i.val := by dsimp [p]; omega
        have hjp : j ≤ p := by simp only [Fin.le_def, Fin.lt_def] at *; dsimp [p]; omega
        have hprev := ih p.val (by dsimp [p]; omega) p rfl j
        have hBi : ls.B i ≠ 0 := hB i
        have hBp : ls.B p ≠ 0 := hB p
        rw [hrows i hip j hji]
        change (rk.rowDifference i p / rk.A i p) * rk.rowDifference p j = _
        rw [hprev, ls.beta_succ_left hp hjp hBp]
        rw [show ls.B p = rk.A i p from LowStorage.ofSubdiagonal_B_succ rk hp,
          show ls.A i = rk.rowDifference i p / ls.B i from
            LowStorage.ofSubdiagonal_A_succ rk hp]
        congr 1
        rw [mul_div_cancel₀ _ hBi]
      · rw [rowDifference_self hexp, LowStorage.beta_self]
        rfl
      · rw [rowDifference_eq_zero_of_lt hexp hij, ls.beta_eq_zero_of_lt hij]
  exact ls.toRK_eq_of_rowDifference hexp fun i => hdiff i.val i rfl

end BSeries.RungeKutta
