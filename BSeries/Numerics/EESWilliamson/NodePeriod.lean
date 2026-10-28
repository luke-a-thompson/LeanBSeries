import BSeries.Numerics.EESWilliamson.NodeRecurrence
import BSeries.Algebra.PolynomialPeriod

/-!
# The full node period

The centered nodes extend by their second-order recurrence. A shorter period repeats stability-coefficient blocks and produces an even common factor of `R(X)` and `R(-X)`, contradicting coprimality.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Polynomial Function
open scoped BigOperators
noncomputable section
variable {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)]

/-- Coprimality forces the full period, distinct consecutive node pairs, and nonzero stability coefficients. -/
theorem forwardBackward_node_regularity {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    (∀ k ≤ s, stabilityCoeff rk k ≠ 0) ∧
      Function.Injective (fun i : Fin (s + s - 1) =>
        (rk.forwardBackward.abscissa ⟨i.val, by have := i.isLt; omega⟩,
          rk.forwardBackward.abscissa ⟨i.val + 1, by have := i.isLt; omega⟩)) := by
  let a := 4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)
  let v : Fin (s + s) → R := fun i => 1 - 2 * rk.forwardBackward.abscissa i
  let y := v ⟨1, by omega⟩
  let u := SecondOrder.sequence a 1 y
  have hc₀ : rk.abscissa ⟨0, by omega⟩ = 0 :=
    Finset.sum_eq_zero fun j _ => hexp _ j (by change 0 ≤ j.val; omega)
  have hv₀ : v ⟨0, by omega⟩ = 1 := by
    have h : rk.forwardBackward.abscissa ⟨0, by omega⟩ = rk.abscissa ⟨0, by omega⟩ :=
      abscissa_forwardBackward_left rk ⟨0, by omega⟩
    dsimp [v]
    rw [h, hc₀]
    ring
  have hrec (k : ℕ) (hk : k + 2 < s + s) :
      v ⟨k + 2, hk⟩ - a * v ⟨k + 1, by omega⟩ + v ⟨k, by omega⟩ = 0 := by
    dsimp [v, a]
    linear_combination -2 * forwardBackward_node_recurrence hs hexp hcons hanti k hk
  have hfinite (i : Fin (s + s)) : u i.val = 1 - 2 * rk.forwardBackward.abscissa i := by
    have h := SecondOrder.sequence_eq_of_finite (by omega : 2 ≤ s + s) a v hrec i.val i.isLt
    rw [hv₀] at h
    exact h
  have hshift (i : Fin s) : u (i.val + s) = -u i.val := by
    have hl := hfinite (i.castAdd s)
    have hr := hfinite (i.natAdd s)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hl hr
    rw [Nat.add_comm i.val s, hr, hl,
      abscissa_forwardBackward_right _ hcons, abscissa_forwardBackward_left]
    ring
  have hsign : (SecondOrder.step a ^ s) (1, y) = -(1, y) := by
    rw [SecondOrder.pair]
    apply Prod.ext
    · change u s = -1
      simpa only [u, Nat.zero_add, SecondOrder.sequence_zero] using hshift ⟨0, by omega⟩
    · change u (s + 1) = -y
      simpa only [u, Nat.add_comm 1 s, SecondOrder.sequence_one] using hshift ⟨1, by omega⟩
  have hantis (n : ℕ) : u (n + s) = -u n := SecondOrder.sequence_add_of_neg a 1 y hsign n
  obtain ⟨m, hm, hms, hperiod, hanti_m⟩ := SecondOrder.exists_half_period a y (by omega) hsign
  change ∀ n, u (n + m) = -u n at hanti_m
  have hmin (k : ℕ) (hk : 0 < k) (hkm : k < 2 * m) :
      ¬(u k = u 0 ∧ u (k + 1) = u 1) := by
    intro h
    have hp : IsPeriodicPt (SecondOrder.step a) k (1, y) := by
      change (SecondOrder.step a)^[k] (1, y) = (1, y)
      rw [← Module.End.pow_apply, SecondOrder.pair]
      change (u k, u (k + 1)) = (1, y)
      rw [h.1, h.2]
      simp [u]
    have hle := hp.minimalPeriod_le hk
    rw [hperiod] at hle
    omega
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have hzero (k : ℕ) (hk : s < k) : stabilityCoeff rk k = 0 := by
    rw [← coeff_stabilityPolynomial hexp]
    exact coeff_eq_zero_of_natDegree_lt ((natDegree_stabilityPolynomial_le rk).trans_lt hk)
  have hmaster (i k : ℕ) : stabilityCoeff rk k * (u i + u (i + k)) =
      2 * stabilityCoeff rk (k + 1) * ∑ j ∈ Finset.range (k + 1), u (i + j) := by
    by_cases hk : k < s
    · apply SecondOrder.master_of_two_shifts a u (SecondOrder.recurrence a 1 y) _ _ k _ i
      intro l hl
      have h := forwardBackward_master_centered hexp hcons hdet hanti ht l k (by omega)
      simpa only [← hfinite, Finset.sum_range] using h
    · rw [hzero (k + 1) (by omega), mul_zero, zero_mul]
      by_cases heq : k = s
      · rw [heq, hantis, add_neg_cancel, mul_zero]
      · rw [hzero k (by omega), zero_mul]
  have hblock := SecondOrder.coefficient_blocks u (stabilityCoeff rk) (m := m) rfl hanti_m hmin hmaster
  have hgap := SecondOrder.coefficient_gap u (stabilityCoeff rk) hanti_m hmin hmaster
  have hdeg : (stabilityPolynomial rk).natDegree = s := by
    apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_stabilityPolynomial_le rk)
    rw [coeff_stabilityPolynomial hexp]
    exact stabilityCoeff_last_ne_zero (by omega) hexp hcons hanti
  have hle := SecondOrder.natDegree_le_half_period (stabilityPolynomial rk)
    (separable_stabilityPolynomial_mul_neg (by omega) hexp hcons hanti).isCoprime hm
    (by simpa only [coeff_stabilityPolynomial hexp] using hblock)
    (by simpa only [coeff_stabilityPolynomial hexp] using hgap)
  rw [hdeg] at hle
  have hms' : m = s := by omega
  subst m
  refine ⟨SecondOrder.coefficients_ne_zero u (stabilityCoeff rk) rfl rfl hmin hmaster, ?_⟩
  intro i j hij
  have h₀ := congrArg Prod.fst hij
  have h₁ := congrArg Prod.snd hij
  dsimp only at h₀ h₁
  have hp : (SecondOrder.step a)^[i.val] (1, y) = (SecondOrder.step a)^[j.val] (1, y) := by
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, SecondOrder.pair, SecondOrder.pair]
    apply Prod.ext
    · change u i.val = u j.val
      rw [hfinite ⟨i.val, by have := i.isLt; omega⟩,
        hfinite ⟨j.val, by have := j.isLt; omega⟩, h₀]
    · change u (i.val + 1) = u (j.val + 1)
      rw [hfinite ⟨i.val + 1, by have := i.isLt; omega⟩,
        hfinite ⟨j.val + 1, by have := j.isLt; omega⟩, h₁]
  apply Fin.ext
  exact iterate_injOn_Iio_minimalPeriod
    (by simp only [Set.mem_Iio, hperiod]; have := i.isLt; omega)
    (by simp only [Set.mem_Iio, hperiod]; have := j.isLt; omega) hp

end
end BSeries.RungeKutta
