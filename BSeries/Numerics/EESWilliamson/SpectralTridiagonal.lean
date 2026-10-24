import BSeries.Numerics.EESWilliamson.RootEvaluation
import BSeries.Numerics.EESWilliamson.StagePolynomials

/-!
# The three-term recurrence from root evaluation

The stage polynomials are eigenvectors of the bidiagonal polynomial operator. Evaluation at the roots of the stability polynomial turns that operator into an irreducible tridiagonal matrix. Its diagonal symmetrizer makes multiplication by the independent variable symmetric too. Orthogonality and degree then give the three-term recurrence, without any analysis of collisions with the output node.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Matrix Polynomial
open scoped BigOperators
noncomputable section

local instance spectralTridiagonalInvertibleTwo : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- Root evaluation gives the missing lower zeros of the multiplication matrix. -/
theorem forwardBackward_reverseShift_tridiagonal {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i : Fin s) (j : Fin (s + s)) (hji : j.val + 1 < i.val) :
    rk.forwardBackward.reverseShift (i.castAdd s) j = 0 := by
  have hexpc := isExplicit_forwardBackward rk hexp
  have hsub := forwardBackward_subdiagonal_ne_zero (by omega : 0 < s) hexp hcons hanti
  have hdet := det_krylovMatrix_ne_zero hexpc hsub
  obtain ⟨q, hroot, hphase, horder, hroots⟩ := exists_forwardBackward_spectral_data hs hexp hcons hanti
  have hq : q ≠ 0 := by intro h; simp [h] at hroot
  have hq₁ : q ≠ 1 := by intro h; rw [h, one_pow] at hphase; norm_num at hphase
  have hdist : q ≠ q⁻¹ := by
    intro heq
    have hpow : q ^ 2 = 1 := by
      calc q ^ 2 = q * q⁻¹ := by rw [← heq, pow_two]
           _ = 1 := mul_inv_cancel₀ hq
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    rw [horder] at hdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  obtain ⟨hu₀, hrec⟩ := forwardBackward_centered_recurrence hs hexp hcons hanti
  obtain ⟨A, B, hAB, hform⟩ := secondOrder_root_solution (by omega : 2 ≤ s + s)
    _ q hq hroot hdist (fun k => ((1 - 2 * rk.forwardBackward.abscissa k : ℝ) : ℂ)) hrec hu₀
  have hnorm : ‖q‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := 2 * s)
    (by rw [← horder]; exact pow_orderOf_eq_one q) (by omega)
  have hmodes := reciprocal_modes_ne_zero q A B hnorm hdist hAB
    (1 - 2 * rk.forwardBackward.abscissa ⟨1, by omega⟩)
    (by simpa only [pow_one] using hform ⟨1, by omega⟩)
  have hc (k : Fin (s + s)) : (rk.forwardBackward.abscissa k : ℂ) = spectralNode q A B k.val := by
    have h := hform k
    push_cast at h
    dsimp [spectralNode]
    linear_combination -h / 2
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have hsum (k : ℕ) (hk : k ≤ s) :
      (↑(krylovSubdiagonal t k) : ℂ) = spectralSum q A B k := by
    induction k with
    | zero => simp [spectralSum]
    | succ k ih =>
        have hd := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht
          ⟨k, by omega⟩
        have hd' : (↑(krylovSubdiagonal t (k + 1)) : ℂ) - (↑(krylovSubdiagonal t k) : ℂ) =
            ((1 - 2 * rk.forwardBackward.abscissa ⟨k, by omega⟩ : ℝ) : ℂ) := by exact_mod_cast hd
        rw [hform, ih (by omega)] at hd'
        simpa only [spectralSum, Finset.sum_range_succ, add_comm] using (sub_eq_iff_eq_add.mp hd')
  let x : Fin s → ℂ := fun l => spectralRoot q l.val
  have hxinj : Function.Injective x := by
    intro l m hlm
    have hqm := sub_ne_zero.mpr hq₁
    have hl := pow_ne_zero l.val hq
    have hm := pow_ne_zero m.val hq
    change 2 / ((q - 1) * q ^ l.val) = 2 / ((q - 1) * q ^ m.val) at hlm
    have heq : q ^ l.val = q ^ m.val := by
      field_simp at hlm
      exact hlm.symm
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by simp only [Set.mem_Iio]; have := l.isLt; omega)
      (by simp only [Set.mem_Iio]; have := m.isLt; omega) heq
  have hxroot (l : Fin s) : (stabilityPolynomial rk).eval₂ Complex.ofRealHom (x l) = 0 := by
    rw [eval₂_eq_eval_map]
    exact hroots l.val l.isLt
  let V : Matrix (Fin s) (Fin s) ℂ := rk.krylovMatrix.map Complex.ofReal
  let L := upperBand s (spectralNode q A B) (fun k => spectralSum q A B (k + 1))
  have hLV : L * Vᵀ = Vᵀ * diagonal (fun k => (rk.abscissa k : ℂ)) := by
    ext k l
    have hc₀ : (rk.abscissa k : ℂ) = spectralNode q A B k.val := by
      simpa only [abscissa_forwardBackward_left, Fin.val_castAdd] using hc (k.castAdd s)
    have he := ht ⟨k.val, by have := k.isLt; omega⟩ (l.castAdd s)
    simp only [stageWeight_forwardBackward_left, abscissa_forwardBackward_left] at he
    rw [show rk.forwardBackward.abscissa ⟨k.val, by have := k.isLt; omega⟩ =
      rk.abscissa k from abscissa_forwardBackward_left rk k] at he
    have he' : (rk.abscissa l : ℂ) * V l k = (rk.abscissa k : ℂ) * V l k +
        (t ⟨k.val, by have := k.isLt; omega⟩ : ℂ) *
          (↑(stageWeight rk (PTree.tallTree (k.val + 1)) l) : ℂ) := by
      dsimp [V, krylovMatrix, Matrix.map_apply]
      exact_mod_cast he
    rw [← krylovSubdiagonal_succ t k.val (by have := k.isLt; omega),
      hsum (k.val + 1) (by have := k.isLt; omega), hc₀] at he'
    simp only [L, upperBand_mul, transpose_apply, mul_diagonal]
    by_cases hk : k.val + 1 < s
    · rw [dite_eq_left hk]
      exact he'.symm.trans (mul_comm ..)
    · rw [dite_eq_right hk]
      rw [stageWeight_tallTree_eq_zero_of_lt hexp (k.val + 1) l
        (by have := l.isLt; omega), Complex.ofReal_zero, mul_zero, add_zero] at he'
      simpa only [add_zero] using he'.symm.trans (mul_comm ..)
  let W := stageEvaluation rk Complex.ofRealHom x
  let H : Matrix (Fin s) (Fin s) ℂ := fun k l =>
    (rk.forwardBackward.reverseShift (k.castAdd s) (l.castAdd s) : ℂ)
  have hW : W.det ≠ 0 := det_stageEvaluation_ne_zero rk Complex.ofRealHom x hxinj
    (det_krylovMatrix_ne_zero hexp (fun k l hkl => by
      have h := hsub (k.castAdd s) (l.castAdd s) hkl
      simpa only [forwardBackward_A_left_left] using h))
  have hTW : rootOperator s q A B * W = W * diagonal (fun k => (rk.abscissa k : ℂ)) := by
    change rootOperator s q A B * (vandermonde x * Vᵀ) =
      (vandermonde x * Vᵀ) * diagonal (fun k => (rk.abscissa k : ℂ))
    rw [← Matrix.mul_assoc, rootOperator_vandermonde q A B hq hq₁ hAB hphase,
      Matrix.mul_assoc, hLV, Matrix.mul_assoc]
  have htri := Matrix.tridiagonal_of_eigenbasis (rootOperator s q A B) W H (by omega) hW
    (fun k => (rk.abscissa k : ℂ)) x (rootOperator_band s q A B)
    (rootOperator_adjacent q A B hmodes.1 hmodes.2 hphase horder) hTW
    (stageEvaluation_mul_reverseShift hexp hsub Complex.ofRealHom x hxroot)
    (fun k l hkl => by
      dsimp [H]
      rw [reverseShift_eq_zero_of_lt hexpc hsub (k.castAdd s) (l.castAdd s) hkl]
      rfl)
  let j' : Fin s := ⟨j.val, by have := i.isLt; omega⟩
  have hj : j'.castAdd s = j := Fin.ext rfl
  have h := htri i j' hji
  dsimp [H] at h
  rw [hj] at h
  exact_mod_cast h

end
end BSeries.RungeKutta
