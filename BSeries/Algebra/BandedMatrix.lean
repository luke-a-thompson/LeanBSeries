/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Products of bidiagonal matrices

Entry formulas for multiplying finite bidiagonal matrices and the upper shift. Natural-number coefficient sequences include the zero boundary values explicitly.
-/

namespace Matrix
open scoped BigOperators

variable {R : Type*} [CommSemiring R] {N : ℕ}

/-- The transpose of the nilpotent shift: it sends `e_(k+1)` to `e_k`. -/
def upperShift (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- A lower bidiagonal matrix with diagonal `c_i` and subdiagonal `q_i`. -/
def lowerBand (N : ℕ) (c q : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  fun i j => (if i = j then c i.val else 0) + (if i.val = j.val + 1 then q i.val else 0)

/-- An upper bidiagonal matrix with diagonal `d_i` and superdiagonal `e_i`. -/
def upperBand (N : ℕ) (d e : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  fun i j => (if i = j then d i.val else 0) + (if j.val = i.val + 1 then e i.val else 0)

theorem lowerBand_mul (c q : ℕ → R) (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (lowerBand N c q * M) i j = c i.val * M i j +
      if hi : 0 < i.val then q i.val * M ⟨i.val - 1, by have := i.isLt; omega⟩ j else 0 := by
  simp only [Matrix.mul_apply, lowerBand, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi, Finset.sum_eq_single (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin N),
      ite_eq_left (by dsimp; omega)]
    · intro k hk hki
      exact ite_eq_right (fun h => hki (Fin.ext (by dsimp; omega)))
    · simp
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (by omega)

theorem upperBand_mul (d e : ℕ → R) (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (upperBand N d e * M) i j = d i.val * M i j +
      if hi : i.val + 1 < N then e i.val * M ⟨i.val + 1, hi⟩ j else 0 := by
  simp only [Matrix.mul_apply, upperBand, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  by_cases hi : i.val + 1 < N
  · rw [dite_eq_left hi, Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin N), ite_eq_left rfl]
    · intro k hk hki
      exact ite_eq_right (fun h => hki (Fin.ext h))
    · simp
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (by have := k.isLt; omega)

@[simp] theorem transpose_lowerBand (c q : ℕ → R) :
    (lowerBand N c q)ᵀ = upperBand N c (fun i => q (i + 1)) := by
  ext i j
  simp only [transpose_apply, lowerBand, upperBand]
  split_ifs <;> simp_all

/-- Right multiplication follows from left multiplication by the transpose. -/
theorem mul_lowerBand (M : Matrix (Fin N) (Fin N) R) (c q : ℕ → R) (i j : Fin N) :
    (M * lowerBand N c q) i j = M i j * c j.val +
      if hj : j.val + 1 < N then M i ⟨j.val + 1, hj⟩ * q (j.val + 1) else 0 := by
  have h := upperBand_mul c (fun k => q (k + 1)) Mᵀ j i
  rw [← transpose_lowerBand, ← transpose_mul] at h
  simpa only [transpose_apply, mul_comm] using h

end Matrix
