import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Quadratic identities for bidiagonal polynomial operators

The node and subdiagonal recurrences give a quadratic relation with multiplication by `X`. Its commutator supplies the dual relation, which forces a three-term recurrence in any degree-ordered eigenbasis.
-/

namespace Polynomial
open Module

noncomputable section
variable {R : Type*} [CommRing R]

/-- The polynomial operator with diagonal `c k` and lowering coefficient `t k`.
The coefficient `t 0` is zero in applications. -/
def bidiagonal (c t : ℕ → R) : R[X] →ₗ[R] R[X] :=
  (basisMonomials R).constr R fun k => c k • X ^ k + t k • X ^ (k - 1)

@[simp] theorem bidiagonal_X_pow (c t : ℕ → R) (k : ℕ) :
    bidiagonal c t (X ^ k) = c k • X ^ k + t k • X ^ (k - 1) := by
  simpa only [bidiagonal, coe_basisMonomials, monomial_one_right_eq_X_pow] using (basisMonomials R).constr_basis R
    (fun k => c k • X ^ k + t k • X ^ (k - 1)) k

@[simp] theorem bidiagonal_one (c t : ℕ → R) :
    bidiagonal c t 1 = (c 0 + t 0) • (1 : R[X]) := by
  simpa only [pow_zero, Nat.zero_sub, add_smul] using bidiagonal_X_pow c t 0

@[simp] theorem bidiagonal_X (c t : ℕ → R) :
    bidiagonal c t X = c 1 • X + t 1 • (1 : R[X]) := by
  simpa only [pow_one, Nat.sub_self, pow_zero] using bidiagonal_X_pow c t 1

theorem coeff_bidiagonal (c t : ℕ → R) (ht₀ : t 0 = 0) (p : R[X]) (k : ℕ) :
    (bidiagonal c t p).coeff k = c k * p.coeff k + t (k + 1) * p.coeff (k + 1) := by
  have h : (lcoeff R k).comp (bidiagonal c t) =
      c k • lcoeff R k + t (k + 1) • lcoeff R (k + 1) := by
    apply (basisMonomials R).ext
    intro m
    simp only [coe_basisMonomials, monomial_one_right_eq_X_pow, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply, lcoeff_apply, bidiagonal_X_pow,
      coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul]
    by_cases hm : m = 0
    · subst m
      by_cases hk : k = 0 <;> simp [ht₀, hk]
    · have hmk : k = m - 1 ↔ k + 1 = m := by omega
      simp only [hmk]
      split_ifs <;> simp_all
  exact LinearMap.congr_fun h p

/-- The quadratic relation with multiplication by the variable. -/
def quadraticRelation (D : R[X] →ₗ[R] R[X]) (a b d e : R) : R[X] →ₗ[R] R[X] :=
  let Z := LinearMap.mulLeft R (X : R[X])
  a • (Z * Z * D + D * Z * Z) + b • (Z * D * Z) + d • (Z * Z) + (2 * e) • Z

/-- The dual quadratic expression, obtained by commuting the relation with `D`. -/
def quadraticDual (D : R[X] →ₗ[R] R[X]) (a b d e : R) : R[X] →ₗ[R] R[X] :=
  let Z := LinearMap.mulLeft R (X : R[X])
  a • (D * D * Z + Z * D * D) + b • (D * Z * D) + d • (D * Z + Z * D) +
    (2 * e) • D

theorem quadraticDual_commutator (D : R[X] →ₗ[R] R[X]) (a b d e : R) (p : R[X]) :
    quadraticDual D a b d e (X * p) - X * quadraticDual D a b d e p =
      D (quadraticRelation D a b d e p) - quadraticRelation D a b d e (D p) := by
  simp only [quadraticDual, quadraticRelation, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, map_add, map_smul,
    mul_add, mul_smul_comm, mul_assoc]
  module

theorem quadraticRelation_X_pow (c t : ℕ → R) (a b d e : R) (ht₀ : t 0 = 0)
    (k : ℕ)
    (hc : a * (c k + c (k + 2)) + b * c (k + 1) + d = 0)
    (ht : a * (t k + t (k + 2)) + b * t (k + 1) + 2 * e = 0) :
    quadraticRelation (bidiagonal c t) a b d e (X ^ k) = 0 := by
  have hc' : (a * (c k + c (k + 2)) + b * c (k + 1) + d) •
      (X ^ (k + 2) : R[X]) = 0 := by rw [hc, zero_smul]
  have ht' : (a * (t k + t (k + 2)) + b * t (k + 1) + 2 * e) •
      (X ^ (k + 1) : R[X]) = 0 := by rw [ht, zero_smul]
  simp only [quadraticRelation, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, ← pow_succ', bidiagonal_X_pow,
    map_add, map_smul]
  cases k with
  | zero =>
      simp only [Nat.zero_sub, ht₀, zero_smul, add_zero,
        Nat.zero_add] at *
      linear_combination (norm := module) hc' + ht'
  | succ k =>
      simp only [Nat.add_sub_cancel]
      linear_combination (norm := module) hc' + ht'

/-- Commutation with `X` determines the dual relation on the required finite range. -/
theorem quadraticDual_X_pow (c t : ℕ → R) (a b d : R) {N : ℕ}
    (hc₀ : c 0 = 0) (ht₀ : t 0 = 0) (ht₁ : t 1 = 1)
    (hrel : ∀ k < N, quadraticRelation (bidiagonal c t) a b d (a * c 1 + d) (X ^ k) = 0)
    (k : ℕ) (hk : k ≤ N) :
    quadraticDual (bidiagonal c t) a b d (a * c 1 + d) (X ^ k) =
      (a * c 1 + d) • (c 1 • X ^ (k + 1) + X ^ k) := by
  induction k with
  | zero =>
      simp only [pow_zero, pow_one, quadraticDual, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, bidiagonal_one, bidiagonal_X,
        hc₀, ht₀, ht₁, zero_add, zero_smul, one_smul, mul_one,
        map_zero, map_add, map_smul, mul_add]
      module
  | succ k ih =>
      have hD : quadraticRelation (bidiagonal c t) a b d (a * c 1 + d)
          (bidiagonal c t (X ^ k)) = 0 := by
        rw [bidiagonal_X_pow, map_add, map_smul, map_smul,
          hrel k (by omega), hrel (k - 1) (by omega)]
        simp
      have h := quadraticDual_commutator (bidiagonal c t) a b d (a * c 1 + d) (X ^ k)
      rw [hrel k (by omega), map_zero, hD, sub_self, sub_eq_zero,
        ih (by omega)] at h
      rw [pow_succ', h]
      simp only [mul_smul_comm, mul_add, ← pow_succ']

theorem quadraticDual_apply (c t : ℕ → R) (a b d : R) {N : ℕ}
    (hc₀ : c 0 = 0) (ht₀ : t 0 = 0) (ht₁ : t 1 = 1)
    (hrel : ∀ k < N, quadraticRelation (bidiagonal c t) a b d (a * c 1 + d) (X ^ k) = 0)
    (p : R[X]) (hp : p.natDegree ≤ N) :
    quadraticDual (bidiagonal c t) a b d (a * c 1 + d) p =
      (a * c 1 + d) • (c 1 • (X * p) + p) := by
  rw [p.as_sum_range_C_mul_X_pow]
  simp only [← smul_eq_C_mul, map_sum, map_smul, Finset.mul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [quadraticDual_X_pow c t a b d hc₀ ht₀ ht₁ hrel k
    (by have := Finset.mem_range.mp hk; omega)]
  simp only [pow_succ', mul_smul_comm]
  module

/-- Consecutive nodes have the same quadratic invariant. -/
theorem secondOrder_invariant (c : ℕ → R) (a b d : R) {N : ℕ} (hc₀ : c 0 = 0)
    (hc : ∀ k, k + 2 < N → a * (c k + c (k + 2)) + b * c (k + 1) + d = 0)
    (k : ℕ) (hk : k + 1 < N) :
    a * (c k ^ 2 + c (k + 1) ^ 2) + b * c k * c (k + 1) +
      d * (c k + c (k + 1)) = (a * c 1 + d) * c 1 := by
  induction k with
  | zero => rw [hc₀]; ring
  | succ k ih =>
      linear_combination ih (by omega) + (c (k + 2) - c k) * hc k hk

theorem secondOrder_adjacent_product (c : ℕ → R) (a b d : R) {N : ℕ} (hc₀ : c 0 = 0)
    (hc : ∀ k, k + 2 < N → a * (c k + c (k + 2)) + b * c (k + 1) + d = 0)
    (k : ℕ) (hk : k + 2 < N) :
    a * c k * c (k + 2) =
      a * c (k + 1) ^ 2 + d * c (k + 1) - (a * c 1 + d) * c 1 := by
  linear_combination c k * hc k hk - secondOrder_invariant c a b d hc₀ hc k (by omega)

/-- Summing the centered nodes gives the companion recurrence for the lowering coefficients. -/
theorem secondOrder_lowering_recurrence (c t : ℕ → R) (a b d : R) {N : ℕ}
    (ht₀ : t 0 = 0) (ht₁ : t 1 = 1) (habd : 2 * a + b + 2 * d = 0)
    (hc : ∀ k, k + 2 < N → a * (c k + c (k + 2)) + b * c (k + 1) + d = 0)
    (ht : ∀ k, k < N → t (k + 1) - t k = 1 - 2 * c k)
    (k : ℕ) (hk : k + 2 < N) :
    a * (t k + t (k + 2)) + b * t (k + 1) + 2 * (a * c 1 + d) = 0 := by
  induction k with
  | zero =>
      have h := ht 1 (by omega)
      rw [ht₁] at h
      rw [ht₀, ht₁]
      linear_combination a * h + habd
  | succ k ih =>
      linear_combination ih (by omega) + a * ht k (by omega) +
        a * ht (k + 2) (by omega) + b * ht (k + 1) (by omega) -
          2 * hc k (by omega) + habd

/-- In an eigenbasis, the dual relation annihilates each coefficient away from its quadratic roots. -/
theorem quadraticDual_eigen_coefficient {ι : Type*} [Fintype ι]
    (D : R[X] →ₗ[R] R[X]) (a b d e γ : R) (P : ι → R[X]) (c H : ι → R)
    (hP : LinearIndependent R P) (hD : ∀ j, D (P j) = c j • P j) (i j : ι)
    (hX : X * P i = ∑ j, H j • P j)
    (hdual : quadraticDual D a b d e (P i) = e • (γ • (X * P i) + P i))
    (hji : j ≠ i) :
    H j * (a * (c j ^ 2 + c i ^ 2) + b * c i * c j + d * (c j + c i) - e * γ) = 0 := by
  classical
  let F : R[X] →ₗ[R] R[X] := a • (D * D) + (b * c i + d) • D +
    (a * c i ^ 2 + d * c i - e * γ) • LinearMap.id
  have hF (j : ι) : F (P j) =
      (a * (c j ^ 2 + c i ^ 2) + b * c i * c j + d * (c j + c i) - e * γ) • P j := by
    simp only [F, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.id_apply, hD, map_smul]
    module
  have hFi : F (X * P i) = (e * (1 - 2 * c i)) • P i := by
    simp only [quadraticDual, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, LinearMap.mulLeft_apply, hD, map_smul] at hdual
    simp only [F, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.id_apply]
    linear_combination (norm := module) hdual
  have hsum :
      (∑ j, (H j * (a * (c j ^ 2 + c i ^ 2) + b * c i * c j +
        d * (c j + c i) - e * γ)) • P j) =
      ∑ j, (if j = i then e * (1 - 2 * c i) else 0) • P j := by
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hFi, hX, map_sum]
    simp only [map_smul, hF, smul_smul]
  simpa only [hji, ite_false] using hP.eq_coords_of_eq hsum j

end
end Polynomial
