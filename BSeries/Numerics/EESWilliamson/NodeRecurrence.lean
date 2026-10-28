/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.BlockSwap

/-!
# The node recurrence forced by the antisymmetric order condition

The diagonal and second superdiagonal of the block-swap identity determine a second-order recurrence for the composite abscissae. Regularity excludes its singular coefficient `r₃ = 1/4`.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)] {s : ℕ}

/-- The diagonal part of the master identity gives successive differences of the bidiagonal coefficients. -/
theorem forwardBackward_subdiagonal_difference {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (i : Fin (s + s)) :
    krylovSubdiagonal t (i.val + 1) - krylovSubdiagonal t i.val =
      1 - 2 * rk.forwardBackward.abscissa i := by
  have h := forwardBackward_master_identity hexp hcons hdet hanti ht i i le_rfl
  simp only [Nat.sub_self, Nat.zero_add, stabilityCoeff_one_of_consistent hcons] at h
  change (_ + _ - 1) * 1 + _ * 1 = 0 at h
  linear_combination h

/-- The second superdiagonal gives the undivided node recurrence. -/
theorem forwardBackward_node_recurrence_raw {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (k : ℕ) (hk : k + 2 < s + s) :
    (1 - 4 * stabilityCoeff rk 3) *
        (rk.forwardBackward.abscissa ⟨k, by omega⟩ +
          rk.forwardBackward.abscissa ⟨k + 2, hk⟩) -
      4 * stabilityCoeff rk 3 * rk.forwardBackward.abscissa ⟨k + 1, by omega⟩ +
        6 * stabilityCoeff rk 3 - 1 = 0 := by
  let i₀ : Fin (s + s) := ⟨k, by omega⟩
  let i₁ : Fin (s + s) := ⟨k + 1, by omega⟩
  let i₂ : Fin (s + s) := ⟨k + 2, hk⟩
  have hm := forwardBackward_master_identity hexp hcons hdet hanti ht i₀ i₂ (by
    change k ≤ k + 2; omega)
  have h₀ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₀
  have h₁ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₁
  have h₂ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₂
  simp only [i₀, i₁, i₂, Nat.add_sub_cancel_left] at hm h₀ h₁ h₂
  rw [stabilityCoeff_two_of_hasAntisymOrder hs hexp hcons hanti] at hm
  linear_combination 2 * hm - 2 * stabilityCoeff rk 3 * h₀ -
    2 * stabilityCoeff rk 3 * h₁ - 2 * stabilityCoeff rk 3 * h₂

/-- If `r₃ = 1/4`, the node recurrence forces the first backward abscissa to be `1/2`, contradicting its value `1`. -/
theorem stabilityCoeff_three_ne_quarter {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityCoeff rk 3 ≠ 1 / 4 := by
  intro hr
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have h := forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht
    (s - 1) (by omega)
  have hc₀ : rk.abscissa ⟨0, by omega⟩ = 0 := by
    exact Finset.sum_eq_zero fun j _ => hexp _ j (by change 0 ≤ j.val; omega)
  have heq : (⟨s - 1 + 1, by omega⟩ : Fin (s + s)) =
      (⟨0, by omega⟩ : Fin s).natAdd s := Fin.ext (by simp; omega)
  rw [hr, heq, abscissa_forwardBackward_right _ hcons, hc₀] at h
  norm_num at h

/-- Normalizing gives the homogeneous recurrence for the centered nodes. -/
theorem forwardBackward_node_recurrence {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (k : ℕ) (hk : k + 2 < s + s) :
    rk.forwardBackward.abscissa ⟨k + 2, hk⟩ -
        (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)) *
          rk.forwardBackward.abscissa ⟨k + 1, by omega⟩ +
        rk.forwardBackward.abscissa ⟨k, by omega⟩ =
      1 - 2 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) := by
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have hraw := forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht k hk
  have hden : 1 - 4 * stabilityCoeff rk 3 ≠ 0 := by
    intro h
    apply stabilityCoeff_three_ne_quarter hs hexp hcons hanti
    linear_combination -h / 4
  field_simp
  linear_combination hraw

/-- The master identity after centering the nodes and telescoping the bidiagonal differences. -/
theorem forwardBackward_master_centered {s : ℕ}
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (i k : ℕ) (hik : i + k < s + s) :
    stabilityCoeff rk k * ((1 - 2 * rk.forwardBackward.abscissa ⟨i, by omega⟩) +
        (1 - 2 * rk.forwardBackward.abscissa ⟨i + k, hik⟩)) =
      2 * stabilityCoeff rk (k + 1) *
        ∑ j : Fin (k + 1), (1 - 2 * rk.forwardBackward.abscissa
          ⟨i + j.val, by have := j.isLt; omega⟩) := by
  have hq (k : ℕ) (hik : i + k < s + s) :
      krylovSubdiagonal t (i + k + 1) - krylovSubdiagonal t i =
        ∑ j : Fin (k + 1), (1 - 2 * rk.forwardBackward.abscissa
          ⟨i + j.val, by have := j.isLt; omega⟩) := by
    have h := Finset.sum_range_sub (fun j => krylovSubdiagonal t (i + j)) (k + 1)
    rw [Finset.sum_range] at h
    simp only [← Nat.add_assoc, Nat.add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    exact forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht
      ⟨i + j.val, by have := j.isLt; omega⟩
  have h := forwardBackward_master_identity hexp hcons hdet hanti ht
    ⟨i, by omega⟩ ⟨i + k, hik⟩ (by change i ≤ i + k; omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [hq k hik] at h
  linear_combination -2 * h

end

end BSeries.RungeKutta
