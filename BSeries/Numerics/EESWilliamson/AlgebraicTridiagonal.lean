import BSeries.Numerics.EESWilliamson.NodeRecurrence
import BSeries.Numerics.EESWilliamson.StagePolynomials
import BSeries.Numerics.EESWilliamson.NodeNoncollision

/-!
# The algebraic three-term recurrence

The two scalar recurrences imply a quadratic operator identity. In the stage-polynomial eigenbasis, its dual relation excludes every coefficient outside the three adjacent degrees.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Matrix Polynomial
open scoped BigOperators
noncomputable section

variable {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)]

/-- The dual quadratic relation factors at the two neighboring abscissae. -/
theorem forwardBackward_reverseShift_quadratic {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i : Fin s) (hi : 0 < i.val) (j : Fin (s + s)) (hji : j.val + 1 < i.val) :
    (rk.forwardBackward.abscissa j - rk.abscissa ⟨i.val - 1, by omega⟩) *
      (rk.forwardBackward.abscissa j -
        rk.forwardBackward.abscissa ⟨i.val + 1, by have := i.isLt; omega⟩) *
      rk.forwardBackward.reverseShift (i.castAdd s) j = 0 := by
  classical
  have hexpc := isExplicit_forwardBackward rk hexp
  have hsub := forwardBackward_subdiagonal_ne_zero (by omega : 0 < s) hexp hcons hanti
  have hdet := det_krylovMatrix_ne_zero hexpc hsub
  obtain ⟨t, ht, ht₁⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  let c : ℕ → R := fun k => if hk : k < s + s then rk.forwardBackward.abscissa ⟨k, hk⟩ else 0
  let a := 1 - 4 * stabilityCoeff rk 3
  let b := -4 * stabilityCoeff rk 3
  let d := 6 * stabilityCoeff rk 3 - 1
  have hc (k : Fin (s + s)) : c k.val = rk.forwardBackward.abscissa k := by
    simp only [c, dite_eq_left k.isLt]
  have hc₀ : c 0 = 0 := by
    rw [hc ⟨0, by omega⟩]
    exact Finset.sum_eq_zero fun j _ => hexpc _ j (by change 0 ≤ j.val; omega)
  have ht₀ : krylovSubdiagonal t 0 = 0 := by simp
  have ht₁' : krylovSubdiagonal t 1 = 1 := by
    simpa only [krylovSubdiagonal_succ t 0 (by omega)] using ht₁
  have hrec (k : ℕ) (hk : k + 2 < s + s) :
      a * (c k + c (k + 2)) + b * c (k + 1) + d = 0 := by
    rw [hc ⟨k, by omega⟩, hc ⟨k + 2, hk⟩, hc ⟨k + 1, by omega⟩]
    linear_combination forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht k hk
  have hdiff (k : ℕ) (hk : k < s + s) :
      krylovSubdiagonal t (k + 1) - krylovSubdiagonal t k = 1 - 2 * c k := by
    rw [hc ⟨k, hk⟩]
    exact forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht ⟨k, hk⟩
  have hrel (k : ℕ) (hk : k < s) :
      quadraticRelation (Polynomial.bidiagonal c (krylovSubdiagonal t)) a b d
        (a * c 1 + d) (X ^ k) = 0 :=
    quadraticRelation_X_pow c _ a b d _ ht₀ k (hrec k (by omega))
      (secondOrder_lowering_recurrence c _ a b d ht₀ ht₁' (by dsimp [a, b, d]; ring)
        hrec hdiff k (by omega))
  have hdual := quadraticDual_apply c _ a b d hc₀ ht₀ ht₁' hrel
    (stagePolynomial rk.forwardBackward (i.castAdd s))
    (le_trans (natDegree_stagePolynomial_le hexpc _) (by simp only [Fin.val_castAdd]; omega))
  have hX : X * stagePolynomial rk.forwardBackward (i.castAdd s) =
      ∑ j, rk.forwardBackward.reverseShift (i.castAdd s) j • stagePolynomial rk.forwardBackward j := by
    simpa only [smul_eq_C_mul] using
      (reverseShift_stagePolynomial hexpc hdet (i.castAdd s)
        (by simp only [Fin.val_castAdd]; have := i.isLt; omega)).symm
  have h := quadraticDual_eigen_coefficient _ a b d _ (c 1)
    (stagePolynomial rk.forwardBackward) rk.forwardBackward.abscissa
    (rk.forwardBackward.reverseShift (i.castAdd s))
    (linearIndependent_stagePolynomial hexpc hdet) (ht.stagePolynomial hexpc c hc)
    (i.castAdd s) j hX hdual (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have hsum := hrec (i.val - 1) (by have := i.isLt; omega)
  have hprod := secondOrder_adjacent_product c a b d hc₀ hrec (i.val - 1)
    (by have := i.isLt; omega)
  have hprev : i.val - 1 + 1 = i.val := by omega
  have hnext : i.val - 1 + 2 = i.val + 1 := by omega
  rw [hprev, hnext] at hsum hprod
  have ha : a ≠ 0 := by
    intro h
    apply stabilityCoeff_three_ne_quarter hs hexp hcons hanti
    dsimp [a] at h
    linear_combination -h / 4
  apply (mul_eq_zero.mp (show a *
      ((rk.forwardBackward.abscissa j - rk.abscissa ⟨i.val - 1, by omega⟩) *
        (rk.forwardBackward.abscissa j -
          rk.forwardBackward.abscissa ⟨i.val + 1, by have := i.isLt; omega⟩) *
        rk.forwardBackward.reverseShift (i.castAdd s) j) = 0 from ?_)).resolve_left ha
  have hci : c i.val = rk.forwardBackward.abscissa (i.castAdd s) := hc (i.castAdd s)
  rw [hci, hc ⟨i.val - 1, by omega⟩,
    hc ⟨i.val + 1, by have := i.isLt; omega⟩] at hsum hprod
  have hleft : rk.forwardBackward.abscissa ⟨i.val - 1, by omega⟩ =
      rk.abscissa ⟨i.val - 1, by omega⟩ :=
    abscissa_forwardBackward_left rk ⟨i.val - 1, by omega⟩
  rw [hleft] at hsum hprod
  linear_combination h - rk.forwardBackward.reverseShift (i.castAdd s) j *
    rk.forwardBackward.abscissa j * hsum + rk.forwardBackward.reverseShift (i.castAdd s) j * hprod

/-- Distinct neighboring eigenvalues cancel the two factors in the quadratic identity. -/
theorem forwardBackward_reverseShift_tridiagonal {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i : Fin s) (j : Fin (s + s)) (hji : j.val + 1 < i.val) :
    rk.forwardBackward.reverseShift (i.castAdd s) j = 0 := by
  have hinj := abscissa_injective_of_hasAntisymOrder hs hexp hcons hanti
  let j' : Fin s := ⟨j.val, by have := i.isLt; omega⟩
  have hcj : rk.forwardBackward.abscissa j = rk.abscissa j' := by
    have hj : j'.castAdd s = j := Fin.ext rfl
    rw [← hj, abscissa_forwardBackward_left]
  have h := forwardBackward_reverseShift_quadratic hs hexp hcons hanti i (by omega) j hji
  rw [hcj] at h
  apply (mul_eq_zero.mp h).resolve_left
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    have h := congrArg Fin.val (hinj h)
    dsimp [j'] at h
    omega
  · apply sub_ne_zero.mpr
    by_cases hi : i.val + 1 < s
    · have hcnext : rk.forwardBackward.abscissa ⟨i.val + 1, by have := i.isLt; omega⟩ =
          rk.abscissa ⟨i.val + 1, hi⟩ := abscissa_forwardBackward_left rk ⟨i.val + 1, hi⟩
      rw [hcnext]
      intro h
      have h := congrArg Fin.val (hinj h)
      dsimp [j'] at h
      omega
    · have heq : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (s + s)) =
          (⟨0, by omega⟩ : Fin s).natAdd s := Fin.ext (by simp; have := i.isLt; omega)
      have hc₀ : rk.abscissa ⟨0, by omega⟩ = 0 :=
        Finset.sum_eq_zero fun j _ => hexp _ j (by change 0 ≤ j.val; omega)
      rw [heq, abscissa_forwardBackward_right _ hcons, hc₀, sub_zero]
      exact abscissa_ne_one_of_lt_last hs hexp hcons hanti j' (by dsimp [j']; have := i.isLt; omega)

end
end BSeries.RungeKutta
