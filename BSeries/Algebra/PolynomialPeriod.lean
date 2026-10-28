import BSeries.Algebra.SecondOrderPeriod
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Basic

/-!
# Polynomial coefficients along a periodic recurrence

The centered master identity repeats coefficient blocks of length `2m`. Coefficients in the second half of each block vanish, so a shorter node period would give a nonconstant even factor shared by `P(X)` and `P(-X)`.
-/

namespace SecondOrder
open Polynomial
open scoped BigOperators
noncomputable section
variable {R : Type*} [Field R] [CharZero R]

omit [CharZero R] in
/-- The master identity extends from its first two shifts by the node recurrence. -/
theorem master_of_two_shifts (a : R) (u : ℕ → R)
    (hu : ∀ i, u (i + 2) - a * u (i + 1) + u i = 0) (r r' : R) (k : ℕ)
    (hm : ∀ i ≤ 1, r * (u i + u (i + k)) =
      2 * r' * ∑ j ∈ Finset.range (k + 1), u (i + j)) :
    ∀ i, r * (u i + u (i + k)) = 2 * r' * ∑ j ∈ Finset.range (k + 1), u (i + j) := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero => exact hm 0 (by omega)
  | one => exact hm 1 (by omega)
  | more i ih₀ ih₁ =>
      have hsum : (∑ j ∈ Finset.range (k + 1),
          (u (i + j + 2) - a * u (i + j + 1) + u (i + j))) = 0 :=
        Finset.sum_eq_zero fun j _ => hu (i + j)
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
      have hi := hu i
      have hik := hu (i + k)
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at ih₀ ih₁ hsum hi hik ⊢
      linear_combination a * ih₁ - ih₀ + r * hi + r * hik - 2 * r' * hsum

/-- Every full block is a scalar multiple of the initial block. -/
theorem coefficient_blocks (u r : ℕ → R) {m : ℕ} (hr₀ : r 0 = 1)
    (hanti : ∀ i, u (i + m) = -u i)
    (hmin : ∀ k, 0 < k → k < 2 * m → ¬(u k = u 0 ∧ u (k + 1) = u 1))
    (hmaster : ∀ i k, r k * (u i + u (i + k)) =
      2 * r (k + 1) * ∑ j ∈ Finset.range (k + 1), u (i + j))
    (l k : ℕ) (hk : k < 2 * m) : r (2 * m * l + k) = r (2 * m * l) * r k := by
  have hp := periodic_of_antiperiod u m hanti
  induction k with
  | zero => simp [hr₀]
  | succ k ih =>
      obtain ⟨i, hi⟩ := exists_sum_ne_zero u (by omega : 0 < k + 1) hk hmin
      have h₀ := hmaster i k
      have h₁ := hmaster i (2 * m * l + k)
      have hshift : u (i + (2 * m * l + k)) = u (i + k) := by
        have h := hp.nat_mul l (i + k)
        change u (i + k + l * (2 * m)) = u (i + k) at h
        rw [Nat.mul_comm l] at h
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      rw [hshift, ih (by omega), Nat.add_assoc, sum_length_periodic u m hanti] at h₁
      apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : R) ≠ 0) hi)
      linear_combination -h₁ + r (2 * m * l) * h₀

/-- The second half of the initial coefficient block vanishes. -/
theorem coefficient_gap (u r : ℕ → R) {m : ℕ}
    (hanti : ∀ i, u (i + m) = -u i)
    (hmin : ∀ k, 0 < k → k < 2 * m → ¬(u k = u 0 ∧ u (k + 1) = u 1))
    (hmaster : ∀ i k, r k * (u i + u (i + k)) =
      2 * r (k + 1) * ∑ j ∈ Finset.range (k + 1), u (i + j))
    (k : ℕ) (hmk : m < k) (hk : k < 2 * m) : r k = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      obtain ⟨i, hi⟩ := exists_sum_ne_zero u (by omega : 0 < k) hk hmin
      have h := hmaster i (k - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
      have hz : r (k - 1) * (u i + u (i + (k - 1))) = 0 := by
        by_cases heq : k - 1 = m
        · rw [heq, hanti, add_neg_cancel, mul_zero]
        · rw [ih (k - 1) (by omega) (by omega) (by omega), zero_mul]
      rw [hz] at h
      apply (mul_eq_zero.mp (show r k * (2 * ∑ j ∈ Finset.range k, u (i + j)) = 0 by
        linear_combination -h)).resolve_right
      exact mul_ne_zero (by norm_num) hi

theorem coefficients_ne_zero (u r : ℕ → R) {m : ℕ} (hu₀ : u 0 = 1) (hr₀ : r 0 = 1)
    (hmin : ∀ k, 0 < k → k < 2 * m → ¬(u k = u 0 ∧ u (k + 1) = u 1))
    (hmaster : ∀ i k, r k * (u i + u (i + k)) =
      2 * r (k + 1) * ∑ j ∈ Finset.range (k + 1), u (i + j))
    (k : ℕ) (hk : k ≤ m) : r k ≠ 0 := by
  induction k with
  | zero => rw [hr₀]; exact one_ne_zero
  | succ k ih =>
      obtain ⟨i, hi⟩ := exists_endpoint_ne_zero u hu₀ (by omega : k < m) hmin
      intro h
      have heq := hmaster i k
      rw [h, mul_zero, zero_mul] at heq
      exact mul_ne_zero (ih (by omega)) hi heq

omit [CharZero R] in
/-- Repeated coefficient blocks factor off a polynomial in `X^p`. -/
theorem block_factorization (P : R[X]) {p : ℕ} (hp : 0 < p)
    (hblock : ∀ l k, k < p → P.coeff (p * l + k) = P.coeff (p * l) * P.coeff k) :
    P = (∑ k ∈ Finset.range p, C (P.coeff k) * X ^ k) *
      (∑ l ∈ Finset.range (P.natDegree + 1), C (P.coeff (p * l)) * X ^ (p * l)) := by
  have hgroup (L : ℕ) : (∑ n ∈ Finset.range (p * L), C (P.coeff n) * X ^ n) =
      (∑ k ∈ Finset.range p, C (P.coeff k) * X ^ k) *
        (∑ l ∈ Finset.range L, C (P.coeff (p * l)) * X ^ (p * l)) := by
    induction L with
    | zero => simp
    | succ L ih =>
        rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hblock L k (Finset.mem_range.mp hk), map_mul, pow_add]
        ring
  exact (P.as_sum_range_C_mul_X_pow' (by nlinarith : P.natDegree < p * (P.natDegree + 1))).trans
    (hgroup (P.natDegree + 1))

omit [CharZero R] in
/-- Coprimality with reflection rules out a shorter coefficient block. -/
theorem natDegree_le_half_period (P : R[X]) (hcop : IsCoprime P (P.comp (-X)))
    {m : ℕ} (hm : 0 < m)
    (hblock : ∀ l k, k < 2 * m → P.coeff (2 * m * l + k) = P.coeff (2 * m * l) * P.coeff k)
    (hgap : ∀ k, m < k → k < 2 * m → P.coeff k = 0) : P.natDegree ≤ m := by
  let Q : R[X] := ∑ k ∈ Finset.range (2 * m), C (P.coeff k) * X ^ k
  let E : R[X] := ∑ l ∈ Finset.range (P.natDegree + 1), C (P.coeff (2 * m * l)) * X ^ (2 * m * l)
  have hfactor : P = Q * E := block_factorization P (by omega) hblock
  have hQ : Q.natDegree ≤ m := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    by_cases hkm : k ≤ m
    · exact (natDegree_C_mul_le _ _).trans (by simpa using hkm)
    · simp only [hgap k (by omega) (Finset.mem_range.mp hk), map_zero,
        zero_mul, natDegree_zero, Nat.zero_le]
  have hE : E.comp (-X) = E := by
    simp only [E, sum_comp, mul_comp, C_comp, pow_comp, X_comp]
    apply Finset.sum_congr rfl
    intro l _
    simp only [pow_mul, neg_sq]
  have hunit : IsUnit E := hcop.isUnit_of_dvd' (by rw [hfactor]; exact dvd_mul_left _ _)
    (by rw [hfactor, mul_comp, hE]; exact dvd_mul_left _ _)
  rw [hfactor]
  exact (natDegree_mul_le.trans (by rw [natDegree_eq_zero_of_isUnit hunit, add_zero])).trans hQ

end
end SecondOrder
