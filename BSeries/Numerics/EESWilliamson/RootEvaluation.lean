import BSeries.Numerics.EESWilliamson.Primitive
import BSeries.Algebra.Tridiagonal
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The bidiagonal operator in root-evaluation coordinates

Evaluation at the roots of the stability polynomial changes the monomial bidiagonal operator into an irreducible tridiagonal matrix. This is the finite-dimensional polynomial operator in the spectral proof; no choice of an angle is needed.
-/

namespace BSeries.RungeKutta
open Matrix Polynomial
open scoped BigOperators ComplexConjugate
noncomputable section

/-- Real centered nodes have two nonzero reciprocal-root modes. -/
theorem reciprocal_modes_ne_zero (q A B : ℂ)
    (hnorm : ‖q‖ = 1) (hdist : q ≠ q⁻¹) (hAB : A + B = 1)
    (u : ℝ) (hu : (u : ℂ) = A * q + B * q⁻¹) : A ≠ 0 ∧ B ≠ 0 := by
  have hconj : conj q = q⁻¹ := (Complex.inv_eq_conj hnorm).symm
  constructor
  · intro hA
    have hB : B = 1 := by simpa [hA] using hAB
    rw [hA, hB, zero_mul, one_mul, zero_add] at hu
    have h := congrArg conj hu
    simp only [Complex.conj_ofReal, map_inv₀, hconj, inv_inv] at h
    exact hdist (h.symm.trans hu)
  · intro hB
    have hA : A = 1 := by simpa [hB] using hAB
    rw [hA, hB, zero_mul, one_mul, add_zero] at hu
    have h := congrArg conj hu
    simp only [Complex.conj_ofReal, hconj] at h
    exact hdist (hu.symm.trans h)

/-- Node values expressed in the reciprocal modes `q^k` and `q^(-k)`. -/
def spectralNode (q A B : ℂ) (k : ℕ) : ℂ := (1 - A * q ^ k - B * (q⁻¹) ^ k) / 2

/-- Partial sums of centered nodes, equal to the Krylov subdiagonal coefficients. -/
def spectralSum (q A B : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, (A * q ^ j + B * (q⁻¹) ^ j)

/-- The roots located by polynomial rotation, in orbit order. -/
def spectralRoot (q : ℂ) (j : ℕ) : ℂ := 2 / ((q - 1) * q ^ j)

private def rootLower (q A : ℂ) (j : ℕ) : ℂ := -(A / 2) * (1 - q ^ j)

private def rootUpper (q B : ℂ) (j : ℕ) : ℂ := -(B / 2) * (1 + q ^ (j + 1))

def rootOperator (s : ℕ) (q A B : ℂ) : Matrix (Fin s) (Fin s) ℂ :=
  lowerBand s (fun j => -rootLower q A j - rootUpper q B j) (rootLower q A) +
    upperBand s 0 (rootUpper q B)

private theorem spectralSum_mul (q A B : ℂ) (hq : q ≠ 0) (k : ℕ) :
    (q - 1) * spectralSum q A B k = A * (q ^ k - 1) - B * q * ((q⁻¹) ^ k - 1) := by
  have h₁ := geom_sum_mul q k
  have h₂ := geom_sum_mul q⁻¹ k
  simp only [spectralSum, Finset.sum_add_distrib, ← Finset.mul_sum]
  linear_combination A * h₁ - B * q * h₂ +
    B * (∑ j ∈ Finset.range k, (q⁻¹) ^ j) * (mul_inv_cancel₀ hq)

private theorem spectral_monomial (q A B : ℂ) (hq : q ≠ 0) (hq₁ : q ≠ 1)
    (hAB : A + B = 1) (j k : ℕ) :
    -rootLower q A j * (1 - q ^ k) * spectralRoot q j ^ k +
      -rootUpper q B j * (1 - (q⁻¹) ^ k) * spectralRoot q j ^ k =
        spectralNode q A B k * spectralRoot q j ^ k +
          spectralSum q A B k * (if k = 0 then 0 else spectralRoot q j ^ (k - 1)) := by
  have hqj := pow_ne_zero j hq
  have hqm := sub_ne_zero.mpr hq₁
  have hx : spectralRoot q j * ((q - 1) * q ^ j) = 2 := by
    dsimp [spectralRoot]
    field_simp
  have hsum := spectralSum_mul q A B hq k
  have hscalar :
      -rootLower q A j * (1 - q ^ k) + -rootUpper q B j * (1 - (q⁻¹) ^ k) =
        spectralNode q A B k + ((q - 1) * q ^ j / 2) * spectralSum q A B k := by
    dsimp [rootLower, rootUpper, spectralNode]
    rw [pow_succ]
    linear_combination hAB / 2 - q ^ j * hsum / 2
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, sub_self, mul_zero, spectralNode, ite_true]
    linear_combination hAB / 2
  · rw [ite_eq_right hk, ← add_mul, hscalar, add_mul]
    congr 1
    rw [show spectralRoot q j ^ k = spectralRoot q j ^ (k - 1) * spectralRoot q j from by
      nth_rw 1 [show k = (k - 1) + 1 by omega]
      rw [pow_succ]]
    linear_combination spectralSum q A B k * spectralRoot q j ^ (k - 1) * hx / 2

private theorem spectralRoot_succ (q : ℂ) (hq : q ≠ 0) (j : ℕ) :
    spectralRoot q (j + 1) = q⁻¹ * spectralRoot q j := by
  simp only [spectralRoot, pow_succ, div_mul_eq_div_mul_one_div]
  field_simp

theorem rootOperator_band (s : ℕ) (q A B : ℂ) (i j : Fin s)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) : rootOperator s q A B i j = 0 := by
  have hij : i ≠ j := by intro heq; have := congrArg Fin.val heq; omega
  have h₁ : i.val ≠ j.val + 1 := by omega
  have h₂ : j.val ≠ i.val + 1 := by omega
  simp [rootOperator, lowerBand, upperBand, hij, h₁, h₂]

theorem rootOperator_adjacent {s : ℕ} (q A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hphase : q ^ s = -1) (horder : orderOf q = 2 * s)
    (i j : Fin s) (hij : i.val + 1 = j.val) :
    rootOperator s q A B i j ≠ 0 ∧ rootOperator s q A B j i ≠ 0 := by
  have hne : i ≠ j := by intro heq; have := congrArg Fin.val heq; omega
  have hnot : i.val ≠ j.val + 1 := by omega
  have hp : 1 - q ^ j.val ≠ 0 := sub_ne_zero.mpr (Ne.symm
    (pow_ne_one_of_lt_orderOf (by omega) (by have := j.isLt; omega)))
  have hm : 1 + q ^ j.val ≠ 0 := by
    intro h
    have hpow : q ^ (s + j.val) = 1 := by
      rw [pow_add, hphase]
      linear_combination -h
    exact pow_ne_one_of_lt_orderOf (by omega : s + j.val ≠ 0)
      (by have := j.isLt; omega) hpow
  simpa [rootOperator, lowerBand, upperBand, hne, Ne.symm hne, hnot, hij,
    rootUpper, rootLower] using
    And.intro (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hB (by norm_num : (2 : ℂ) ≠ 0))) hm)
      (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hA (by norm_num : (2 : ℂ) ≠ 0))) hp)

/-- On monomials, the tridiagonal evaluation matrix is the same operator as the transpose of the Krylov bidiagonal matrix. -/
theorem rootOperator_vandermonde {s : ℕ} (q A B : ℂ) (hq : q ≠ 0) (hq₁ : q ≠ 1)
    (hAB : A + B = 1) (hphase : q ^ s = -1) :
    rootOperator s q A B * vandermonde (fun j : Fin s => spectralRoot q j.val) =
      vandermonde (fun j : Fin s => spectralRoot q j.val) *
        upperBand s (spectralNode q A B) (fun k => spectralSum q A B (k + 1)) := by
  ext i k
  have hleft :
      (if hi : 0 < i.val then rootLower q A i.val * spectralRoot q (i.val - 1) ^ k.val else 0) =
        rootLower q A i.val * (q * spectralRoot q i.val) ^ k.val := by
    by_cases hi : 0 < i.val
    · rw [dite_eq_left hi]
      have h := spectralRoot_succ q hq (i.val - 1)
      rw [Nat.sub_add_cancel hi] at h
      rw [h, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    · have hi₀ : i.val = 0 := by omega
      simp [hi₀, rootLower]
  have hright :
      (if hi : i.val + 1 < s then rootUpper q B i.val * spectralRoot q (i.val + 1) ^ k.val else 0) =
        rootUpper q B i.val * (q⁻¹ * spectralRoot q i.val) ^ k.val := by
    by_cases hi : i.val + 1 < s
    · rw [dite_eq_left hi, spectralRoot_succ q hq]
    · have his : i.val + 1 = s := by have := i.isLt; omega
      simp [rootUpper, his, hphase]
  simp only [rootOperator, Matrix.add_mul, Matrix.add_apply, lowerBand_mul, upperBand_mul,
    mul_upperBand, vandermonde_apply, Pi.zero_apply, zero_mul, zero_add]
  rw [hleft, hright]
  have h := spectral_monomial q A B hq hq₁ hAB i.val k.val
  have heq : (if hk : 0 < k.val then spectralRoot q i.val ^ (k.val - 1) *
      spectralSum q A B (k.val - 1 + 1) else 0) =
        spectralSum q A B k.val * (if k.val = 0 then 0 else spectralRoot q i.val ^ (k.val - 1)) := by
    by_cases hk : 0 < k.val
    · rw [dite_eq_left hk, ite_eq_right (by omega), Nat.sub_add_cancel hk, mul_comm]
    · have hk₀ : k.val = 0 := by omega
      simp [hk₀]
  rw [heq]
  simp only [mul_pow] at *
  linear_combination h

end
end BSeries.RungeKutta
