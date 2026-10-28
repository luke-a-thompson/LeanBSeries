import BSeries.Numerics.EESWilliamson.ReverseShift
import BSeries.Algebra.PolynomialBidiagonal

/-!
# Stage polynomials and multiplication by the independent variable

The stage polynomials form a degree-ordered eigenbasis of the bidiagonal Krylov operator. The reverse-shift matrix is the coefficient matrix of multiplication by `X` in this basis.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Matrix Polynomial Module
open scoped BigOperators
noncomputable section
variable {R : Type*} [Field R] {s : ℕ}

def stagePolynomial (rk : RungeKutta (Fin s) R) (i : Fin s) : R[X] := by
  classical
  exact Polynomial.ofFn s (rk.krylovMatrix i)

theorem coeff_stagePolynomial {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (i : Fin s) (k : ℕ) : (stagePolynomial rk i).coeff k = stageWeight rk (PTree.tallTree k) i := by
  classical
  by_cases hk : k < s
  · exact ofFn_coeff_eq_val_of_lt _ hk
  · rw [stagePolynomial, ofFn_coeff_eq_zero_of_ge _ (by omega)]
    exact (stageWeight_tallTree_eq_zero_of_lt hexp k i (by have := i.isLt; omega)).symm

theorem natDegree_stagePolynomial_le {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (i : Fin s) : (stagePolynomial rk i).natDegree ≤ i.val := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_stagePolynomial hexp]
  exact stageWeight_tallTree_eq_zero_of_lt hexp k i hk

theorem linearIndependent_stagePolynomial {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0) :
    LinearIndependent R (stagePolynomial rk) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have h : g ᵥ* rk.krylovMatrix = 0 := by
    ext k
    change (∑ j, g j * stageWeight rk (PTree.tallTree k.val) j) = 0
    have h := congrArg (fun p : R[X] => p.coeff k.val) hg
    simpa only [finsetSum_coeff, coeff_smul, coeff_stagePolynomial hexp, coeff_zero,
      smul_eq_mul] using h
  have heq : g = 0 := Matrix.vecMul_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
      (by simpa using h)
  exact congrFun heq i

/-- The bidiagonal Krylov identity makes each stage polynomial an eigenvector. -/
theorem IsKrylovBidiagonal.stagePolynomial {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (c : ℕ → R) (hc : ∀ k : Fin s, c k.val = rk.abscissa k) (i : Fin s) :
    Polynomial.bidiagonal c (krylovSubdiagonal t) (stagePolynomial rk i) =
      rk.abscissa i • stagePolynomial rk i := by
  ext k
  rw [coeff_bidiagonal c _ (by simp), coeff_smul, smul_eq_mul,
    coeff_stagePolynomial hexp, coeff_stagePolynomial hexp]
  by_cases hk : k + 1 < s
  · rw [krylovSubdiagonal_succ t k hk, hc ⟨k, by omega⟩]
    exact (ht ⟨k, by omega⟩ i).symm
  · rw [stageWeight_tallTree_eq_zero_of_lt hexp (k + 1) i (by have := i.isLt; omega),
      mul_zero, add_zero]
    by_cases hk' : k < s
    · have heq : k = s - 1 := by omega
      rw [hc ⟨k, hk'⟩]
      simpa only [heq] using (diagonal_stageWeight_tallTree_last hexp (by omega) i).symm
    · rw [stageWeight_tallTree_eq_zero_of_lt hexp k i (by have := i.isLt; omega)]
      simp

/-- Away from the last stage, the reverse shift is multiplication by `X` in the stage-polynomial basis. -/
theorem reverseShift_stagePolynomial {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    (i : Fin s) (hi : i.val + 1 < s) :
    (∑ j, C (rk.reverseShift i j) * stagePolynomial rk j) = X * stagePolynomial rk i := by
  classical
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_stagePolynomial hexp]
  by_cases hk : k < s
  · have h := congrFun (reverseShift_mul_chain hdet k hk) i
    change (∑ j, rk.reverseShift i j * stageWeight rk (PTree.tallTree k) j) = _ at h
    rw [h]
    cases k with
    | zero => simp
    | succ k => simp [coeff_stagePolynomial hexp]
  · have hzero (j : Fin s) : stageWeight rk (PTree.tallTree k) j = 0 :=
      stageWeight_tallTree_eq_zero_of_lt hexp k j (by have := j.isLt; omega)
    simp only [hzero, mul_zero, Finset.sum_const_zero]
    cases k with
    | zero => simp
    | succ k =>
        rw [coeff_X_mul, coeff_stagePolynomial hexp]
        exact (stageWeight_tallTree_eq_zero_of_lt hexp k i (by omega)).symm

theorem stagePolynomial_forwardBackward_output {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) :
    stagePolynomial rk.forwardBackward ((⟨0, hs⟩ : Fin s).natAdd s) = stabilityPolynomial rk := by
  ext k
  rw [coeff_stagePolynomial (isExplicit_forwardBackward rk hexp), coeff_stabilityPolynomial hexp]
  cases k with
  | zero => simp [PTree.tallTree, stageWeightList, stabilityCoeff]
  | succ k =>
      rw [stageWeight_tallTree_succ, forwardBackward_mulVec_right]
      have hz : (∑ j, rk.A ⟨0, hs⟩ j * stageWeight rk.forwardBackward (PTree.tallTree k) (j.natAdd s)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hexp _ j (by change 0 ≤ j.val; omega), zero_mul]
      rw [hz, sub_zero]
      simp only [stageWeight_forwardBackward_left]
      rfl

end
end BSeries.RungeKutta
