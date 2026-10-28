import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Periodic

/-!
# Periods of second-order recurrences

Pairs of consecutive values evolve by a linear map. A sign change after `s` steps gives a minimal period `2m` and a sign change after `m` steps.
-/

namespace SecondOrder
open Function
open scoped BigOperators
noncomputable section
variable {R : Type*} [Field R]

def step (a : R) : (R × R) →ₗ[R] (R × R) where
  toFun v := (v.2, a * v.2 - v.1)
  map_add' v w := by ext <;> simp; ring
  map_smul' r v := by ext <;> simp; ring

def sequence (a x y : R) (n : ℕ) : R := ((step a ^ n) (x, y)).1

theorem pair (a x y : R) (n : ℕ) :
    (step a ^ n) (x, y) = (sequence a x y n, sequence a x y (n + 1)) := by
  apply Prod.ext
  · rfl
  · simp only [sequence, pow_succ', Module.End.mul_apply, step, LinearMap.coe_mk, AddHom.coe_mk]

@[simp] theorem sequence_zero (a x y : R) : sequence a x y 0 = x := rfl
@[simp] theorem sequence_one (a x y : R) : sequence a x y 1 = y := by
  simp [sequence, step]

theorem recurrence (a x y : R) (n : ℕ) :
    sequence a x y (n + 2) - a * sequence a x y (n + 1) + sequence a x y n = 0 := by
  simp [sequence, pow_succ', Module.End.mul_apply, step]

theorem sequence_eq_of_finite {N : ℕ} (hN : 2 ≤ N) (a : R) (u : Fin N → R)
    (hu : ∀ (k : ℕ) (hk : k + 2 < N),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (k : ℕ) (hk : k < N) :
    sequence a (u ⟨0, by omega⟩) (u ⟨1, by omega⟩) k = u ⟨k, hk⟩ := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp
  | more k ih₀ ih₁ =>
      linear_combination recurrence a (u ⟨0, by omega⟩) (u ⟨1, by omega⟩) k -
        hu k hk + a * ih₁ (by omega) - ih₀ (by omega)

theorem sequence_add_of_neg (a x y : R) {s : ℕ}
    (hs : (step a ^ s) (x, y) = -(x, y)) (n : ℕ) :
    sequence a x y (n + s) = -sequence a x y n := by
  simp only [sequence, pow_add, Module.End.mul_apply, hs, map_neg, Prod.fst_neg]

/-- The least positive period is twice the least sign-changing shift. -/
theorem exists_half_period [CharZero R] (a y : R) {s : ℕ} (hs : 0 < s)
    (hsign : (step a ^ s) (1, y) = -(1, y)) :
    ∃ m : ℕ, 0 < m ∧ m ≤ s ∧
      minimalPeriod (step a) (1, y) = 2 * m ∧
      Antiperiodic (sequence a 1 y) m := by
  let p := minimalPeriod (step a) (1, y)
  have hperiod : IsPeriodicPt (step a) (2 * s) (1, y) := by
    change (step a)^[2 * s] (1, y) = (1, y)
    rw [← Module.End.pow_apply, two_mul, pow_add, Module.End.mul_apply, hsign, map_neg, hsign, neg_neg]
  have hp : 0 < p := hperiod.minimalPeriod_pos (by omega)
  let m := s % p
  have hmstep : (step a ^ m) (1, y) = -(1, y) := by
    rw [Module.End.pow_apply]
    exact (iterate_mod_minimalPeriod_eq (f := step a) (x := (1, y)) (n := s)).trans
      (by simpa only [Module.End.pow_apply] using hsign)
  have hm : 0 < m := by
    by_contra h
    have hm₀ : m = 0 := by omega
    rw [hm₀, pow_zero, Module.End.one_apply] at hmstep
    have h := congrArg Prod.fst hmstep
    norm_num at h
  have hmperiod : IsPeriodicPt (step a) (2 * m) (1, y) := by
    change (step a)^[2 * m] (1, y) = (1, y)
    rw [← Module.End.pow_apply, two_mul, pow_add, Module.End.mul_apply,
      hmstep, map_neg, hmstep, neg_neg]
  have hd : p ∣ 2 * m := hmperiod.minimalPeriod_dvd
  have hmlt : m < p := Nat.mod_lt _ hp
  have hpm : p = 2 * m := (Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)).symm
  exact ⟨m, hm, Nat.mod_le _ _, hpm, sequence_add_of_neg a 1 y hmstep⟩

theorem sum_period (u : ℕ → R) (m : ℕ) (hm : Antiperiodic u m) (i : ℕ) :
    ∑ j ∈ Finset.range (2 * m), u (i + j) = 0 := by
  rw [two_mul, Finset.sum_range_add]
  have h (j : ℕ) : u (i + (m + j)) = -u (i + j) := by
    simpa only [Nat.add_assoc, Nat.add_comm m j] using hm (i + j)
  simp only [h, Finset.sum_neg_distrib, add_neg_cancel]

theorem sum_length_periodic (u : ℕ → R) (m : ℕ)
    (hm : Antiperiodic u m) (i l k : ℕ) :
    ∑ j ∈ Finset.range (2 * m * l + k), u (i + j) =
      ∑ j ∈ Finset.range k, u (i + j) := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [Nat.mul_succ, Nat.add_right_comm, Finset.sum_range_add, ih]
      have hz : (∑ j ∈ Finset.range (2 * m), u (i + (2 * m * l + k + j))) = 0 := by
        simpa only [Nat.add_assoc] using sum_period u m hm (i + (2 * m * l + k))
      rw [hz, add_zero]

theorem exists_sum_ne_zero (u : ℕ → R) {p k : ℕ} (hk : 0 < k) (hkp : k < p)
    (hmin : ∀ k, 0 < k → k < p → ¬(u k = u 0 ∧ u (k + 1) = u 1)) :
    ∃ i, (∑ j ∈ Finset.range k, u (i + j)) ≠ 0 := by
  by_contra! h
  have heq (i : ℕ) : u (i + k) = u i := by
    have hs := Finset.sum_range_sub (fun j => u (i + j)) k
    simp only [Finset.sum_sub_distrib, Nat.add_zero] at hs
    have hz : (∑ j ∈ Finset.range k, u (i + (j + 1))) = 0 := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (i + 1)
    rw [hz, h, sub_self, eq_comm, sub_eq_zero] at hs
    exact hs
  exact hmin k hk hkp ⟨by simpa using heq 0, by simpa [Nat.add_comm] using heq 1⟩

theorem exists_endpoint_ne_zero [CharZero R] (u : ℕ → R) (hu₀ : u 0 = 1)
    {m k : ℕ} (hk : k < m)
    (hmin : ∀ k, 0 < k → k < 2 * m → ¬(u k = u 0 ∧ u (k + 1) = u 1)) :
    ∃ i, u i + u (i + k) ≠ 0 := by
  by_contra! h
  have hneg : Antiperiodic u k := fun i => by linear_combination h i
  by_cases hk₀ : k = 0
  · have h := h 0
    rw [hk₀, Nat.add_zero, hu₀] at h
    norm_num at h
  · have hp := hneg.periodic_two_mul
    exact hmin (2 * k) (by omega) (by omega)
      ⟨by simpa using hp 0, by simpa only [Nat.add_comm] using hp 1⟩

end
end SecondOrder
