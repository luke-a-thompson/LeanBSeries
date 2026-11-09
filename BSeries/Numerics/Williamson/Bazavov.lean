/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson.Reconstruction

/-!
# Reconstruction from Bazavov compatibility

For explicit tableaux with nonzero output weights, Bazavov's compatibility condition recovers the Williamson coefficients by dividing by those weights. Subdiagonal entries may vanish. The alternative in `Williamson.Subdiagonal` instead permits zero earlier output weights.

Both reconstructions use the division-free row-difference criterion from `Williamson.Reconstruction`.
-/

namespace BSeries.RungeKutta

universe v

variable {R : Type v}

/-- **Bazavov's compatibility condition** (Bazavov, BIT Numer. Math. 66 (2026), article 38, arXiv:2506.07359, Theorem 2):
`a_{ik} (b_j - a_{kj}) = (a_{ij} - a_{kj}) b_k` whenever `k = j + 1 ≤ i`. -/
def BazavovCondition [CommRing R] {s : ℕ} (rk : RungeKutta (Fin s) R) : Prop :=
  ∀ i j k : Fin s, (j : ℕ) + 1 = (k : ℕ) → k ≤ i →
    rk.A i k * (rk.b j - rk.A k j) = (rk.A i j - rk.A k j) * rk.b k

/-- Williamson 2N tableaux satisfy Bazavov's condition (the forward
direction of Bazavov, arXiv:2506.07359, Theorem 2). -/
theorem IsWilliamson2N.bazavovCondition [CommRing R] {s : ℕ}
    {rk : RungeKutta (Fin s) R} (h : IsWilliamson2N rk) :
    BazavovCondition rk := by
  obtain ⟨ls, rfl⟩ := h
  intro i j k hk hki
  have hjk : j < k := by rw [Fin.lt_def]; omega
  have hji : j < i := lt_of_lt_of_le hjk hki
  rw [ls.toRK_A_succ_self hk, ls.toRK_b_succ hk, ls.toRK_A_of_lt hk hji]
  ring

namespace LowStorage

variable {n : ℕ}

/-- Reconstruct low-storage data from an explicit tableau:
`B_j = a_{j+1,j}` (with `B_{s-1} = b_{s-1}`) and
`A_{j+1} = (b_j - a_{j+1,j}) / b_{j+1}`. -/
def ofTableau [Field R] (rk : RungeKutta (Fin (n + 1)) R) :
    LowStorage (n + 1) R where
  B j := rk.rowAfter j j
  A k :=
    if h : 0 < (k : ℕ) then
      (rk.b ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ -
          rk.A k ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩) / rk.b k
    else 0

theorem ofTableau_B [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    (j : Fin (n + 1)) :
    (ofTableau rk).B j =
      if h : (j : ℕ) + 1 < n + 1 then rk.A ⟨(j : ℕ) + 1, h⟩ j
      else rk.b j :=
  rfl

theorem ofTableau_A [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    (k : Fin (n + 1)) :
    (ofTableau rk).A k =
      if h : 0 < (k : ℕ) then
        (rk.b ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ -
            rk.A k ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩) / rk.b k
      else 0 :=
  rfl

theorem ofTableau_B_of_succ [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    {j k : Fin (n + 1)} (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (ofTableau rk).B j = rk.A k j :=
  rowAfter_succ rk hk j

theorem ofTableau_B_last [Field R] (rk : RungeKutta (Fin (n + 1)) R) :
    (ofTableau rk).B (Fin.last n) = rk.b (Fin.last n) :=
  rowAfter_last rk (Fin.last n)

theorem ofTableau_A_of_succ [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    {j k : Fin (n + 1)} (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (ofTableau rk).A k = (rk.b j - rk.A k j) / rk.b k := by
  have h : 0 < (k : ℕ) := by omega
  rw [ofTableau_A, dite_eq_left h,
    show (⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ : Fin (n + 1)) = j from
      Fin.ext (show (k : ℕ) - 1 = (j : ℕ) by omega)]

end LowStorage

/-- **Bazavov's theorem, converse direction** (Bazavov,
arXiv:2506.07359, Theorem 2): an explicit tableau with nonvanishing weights satisfying the
compatibility condition is Williamson 2N. -/
theorem isWilliamson2N_of_bazavovCondition [Field R] {n : ℕ}
    {rk : RungeKutta (Fin (n + 1)) R} (hexp : IsExplicit rk)
    (hb : ∀ j, rk.b j ≠ 0) (hbaz : BazavovCondition rk) :
    IsWilliamson2N rk := by
  refine ⟨LowStorage.ofTableau rk, ?_⟩
  have hrecb : ∀ j k : Fin (n + 1), (j : ℕ) + 1 = (k : ℕ) →
      rk.b j = (LowStorage.ofTableau rk).B j +
        (LowStorage.ofTableau rk).A k * rk.b k := by
    intro j k hk
    rw [LowStorage.ofTableau_B_of_succ rk hk,
      LowStorage.ofTableau_A_of_succ rk hk, div_mul_cancel₀ _ (hb k)]
    ring
  have hrecA : ∀ i j k : Fin (n + 1), (j : ℕ) + 1 = (k : ℕ) → j < i →
      rk.A i j = (LowStorage.ofTableau rk).B j +
        (LowStorage.ofTableau rk).A k * rk.A i k := by
    intro i j k hk hji
    have hki : k ≤ i := by
      rw [Fin.lt_def] at hji
      rw [Fin.le_def]
      omega
    have h := hbaz i j k hk hki
    have h2 : (rk.b j - rk.A k j) / rk.b k * rk.A i k =
        rk.A i j - rk.A k j := by
      rw [div_mul_eq_mul_div, mul_comm (rk.b j - rk.A k j) (rk.A i k), h,
        mul_div_cancel_right₀ _ (hb k)]
    rw [LowStorage.ofTableau_B_of_succ rk hk,
      LowStorage.ofTableau_A_of_succ rk hk, h2]
    ring
  apply (LowStorage.ofTableau rk).toRK_eq_of_rowDifference hexp
  intro i j
  induction j using Fin.reverseInduction with
  | last =>
    rcases lt_or_eq_of_le (Fin.le_last i) with hi | rfl
    · rw [rowDifference_eq_zero_of_lt hexp hi, LowStorage.beta_eq_zero_of_lt _ hi]
    · rw [rowDifference_self hexp, rowAfter_last, LowStorage.beta_self,
        LowStorage.ofTableau_B_last]
  | cast p ih =>
    have hk : p.castSucc.val + 1 = p.succ.val := rfl
    rcases lt_trichotomy p.castSucc i with hpi | rfl | hip
    · have hafter : rk.rowAfter i p.castSucc = (LowStorage.ofTableau rk).B p.castSucc +
          (LowStorage.ofTableau rk).A p.succ * rk.rowAfter i p.succ := by
        unfold rowAfter
        split
        · apply hrecA _ _ _ hk
          simp only [Fin.lt_def] at hpi ⊢
          omega
        · exact hrecb _ _ hk
      rw [LowStorage.beta_eq _ hk i, ite_eq_right (ne_of_gt hpi), ← ih]
      simp only [rowDifference]
      rw [hafter, hrecA _ _ _ hk hpi]
      ring
    · rw [rowDifference_self hexp, LowStorage.beta_self]
      rfl
    · rw [rowDifference_eq_zero_of_lt hexp hip, LowStorage.beta_eq_zero_of_lt _ hip]

/-- **Bazavov's characterisation of Williamson 2N schemes**
(Bazavov, BIT Numer. Math. 66 (2026), article 38, arXiv:2506.07359, Theorem 2; restated in arXiv:2509.20599, Theorem 3.1): an explicit tableau
with nonvanishing weights is Williamson 2N if and only if it satisfies the
compatibility condition. -/
theorem isWilliamson2N_iff_bazavovCondition [Field R] {n : ℕ}
    {rk : RungeKutta (Fin (n + 1)) R} (hexp : IsExplicit rk)
    (hb : ∀ j, rk.b j ≠ 0) :
    IsWilliamson2N rk ↔ BazavovCondition rk :=
  ⟨IsWilliamson2N.bazavovCondition,
    isWilliamson2N_of_bazavovCondition hexp hb⟩

end BSeries.RungeKutta
