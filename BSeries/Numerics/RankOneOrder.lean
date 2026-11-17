/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.AntisymCriterion
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Polynomial cancellation for rank-one adjoint defects

The polynomial spaces and weighted transpose from Lemma
`ees_antisymmetric_order` in Shmelev et al., `main_sn_2.tex`.
The weighted-transpose identity follows Sanz-Serna (2016), Section 7.
-/

namespace BSeries.RungeKutta

open HopfAlgebras

universe u v

variable {ι : Type u} {R : Type v} [Field R]

/-- Stage vectors obtained by evaluating a polynomial of degree at most `k`. -/
def IsStagePolynomial (c : ι → R) (k : ℕ) (f : ι → R) : Prop :=
  ∃ p : Polynomial R, p.natDegree ≤ k ∧ ∀ i, f i = p.eval (c i)

namespace IsStagePolynomial

variable {c : ι → R} {k l : ℕ} {f g : ι → R}

theorem const (a : R) (k : ℕ) : IsStagePolynomial c k (fun _ => a) :=
  ⟨Polynomial.C a, by simp, by simp⟩

theorem mono (h : IsStagePolynomial c k f) (hkl : k ≤ l) :
    IsStagePolynomial c l f := by
  obtain ⟨p, hp, hf⟩ := h
  exact ⟨p, hp.trans hkl, hf⟩

theorem add (hf : IsStagePolynomial c k f) (hg : IsStagePolynomial c k g) :
    IsStagePolynomial c k (fun i => f i + g i) := by
  obtain ⟨p, hp, hf⟩ := hf
  obtain ⟨q, hq, hg⟩ := hg
  exact ⟨p + q, (Polynomial.natDegree_add_le p q).trans (max_le hp hq),
    fun i => by dsimp only; rw [hf i, hg i, Polynomial.eval_add]⟩

theorem smul (hf : IsStagePolynomial c k f) (a : R) :
    IsStagePolynomial c k (fun i => a * f i) := by
  obtain ⟨p, hp, hf⟩ := hf
  exact ⟨a • p, (Polynomial.natDegree_smul_le a p).trans hp,
    fun i => by dsimp only; rw [hf i, Polynomial.eval_smul, smul_eq_mul]⟩

theorem sum {J : Type*} (s : Finset J) (f : J → ι → R)
    (hf : ∀ j ∈ s, IsStagePolynomial c k (f j)) :
    IsStagePolynomial c k (fun i => ∑ j ∈ s, f j i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using IsStagePolynomial.const (c := c) (0 : R) k
  | @insert j s hj ih =>
      intro hf
      have htail := ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))
      simpa only [Finset.sum_insert hj] using (hf j (Finset.mem_insert_self _ _)).add htail

theorem mul (hf : IsStagePolynomial c k f) (hg : IsStagePolynomial c l g) :
    IsStagePolynomial c (k + l) (fun i => f i * g i) := by
  obtain ⟨p, hp, hf⟩ := hf
  obtain ⟨q, hq, hg⟩ := hg
  exact ⟨p * q, Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq),
    fun i => by dsimp only; rw [hf i, hg i, Polynomial.eval_mul]⟩

theorem sub (hf : IsStagePolynomial c k f) (hg : IsStagePolynomial c k g) :
    IsStagePolynomial c k (fun i => f i - g i) := by
  obtain ⟨p, hp, hf⟩ := hf
  obtain ⟨q, hq, hg⟩ := hg
  exact ⟨p - q, (Polynomial.natDegree_sub_le p q).trans (max_le hp hq),
    fun i => by dsimp only; rw [hf i, hg i, Polynomial.eval_sub]⟩

end IsStagePolynomial

/-- The rank-one perturbation `A + q v^T`, where `v_i = b_i q_i`. -/
def rankOnePerturb (rk : RungeKutta ι R) (q : ι → R) : RungeKutta ι R where
  A i j := rk.A i j + q i * (rk.b j * q j)
  b := rk.b

/-- The reflected weighted transpose used in the sensitivity argument. -/
def rankOneTranspose (rk : RungeKutta ι R) (q : ι → R) (i j : ι) : R :=
  rk.b j - rk.A i j - q i * (rk.b j * q j)

variable [Fintype ι]

/-- The polynomial and rank-one hypotheses of the general order lemma. -/
structure RankOneOrderConditions (rk : RungeKutta ι R) (q c : ι → R) (r : ℕ) : Prop where
  closure : ∀ k, k + 1 < r → ∀ f, IsStagePolynomial c k f →
    IsStagePolynomial c (k + 1) (fun i => ∑ j, rk.A i j * f j)
  annihilation : ∀ k, k < r → ∀ f, IsStagePolynomial c k f →
    ∑ i, rk.b i * q i * f i = 0
  defect : ∀ i j, rk.b i * rk.A i j + rk.b j * rk.A j i =
    rk.b i * rk.b j - (rk.b i * q i) * (rk.b j * q j)

namespace RankOneOrderConditions

variable {rk : RungeKutta ι R} {q c : ι → R} {r k : ℕ}

theorem weightedTranspose (h : RankOneOrderConditions rk q c r) (i j : ι) :
    rk.b i * rankOneTranspose rk q i j = rk.b j * rk.A j i := by
  unfold rankOneTranspose
  linear_combination -h.defect i j

theorem perturb_mul (h : RankOneOrderConditions rk q c r) (hk : k < r)
    {f : ι → R} (hf : IsStagePolynomial c k f) (i : ι) :
    (∑ j, (rankOnePerturb rk q).A i j * f j) = ∑ j, rk.A i j * f j := by
  simp only [rankOnePerturb, add_mul, Finset.sum_add_distrib]
  have hzero := h.annihilation k hk f hf
  simp_rw [mul_assoc] at hzero
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hzero, mul_zero, add_zero]

theorem transpose_closure (h : RankOneOrderConditions rk q c r) (hk : k + 1 < r)
    {f : ι → R} (hf : IsStagePolynomial c k f) :
    IsStagePolynomial c (k + 1) (fun i => ∑ j, rankOneTranspose rk q i j * f j) := by
  have hzero := h.annihilation k (by omega) f hf
  have hpoly := (IsStagePolynomial.const (c := c) (∑ j, rk.b j * f j) (k + 1)).sub
    (h.closure k hk f hf)
  convert hpoly using 1
  funext i
  simp only [rankOneTranspose, sub_mul, Finset.sum_sub_distrib]
  have hlast : (∑ j, q i * (rk.b j * q j) * f j) = 0 := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simpa [mul_assoc] using congrArg (fun x => q i * x) hzero
  rw [hlast, sub_zero]

private theorem order_le_orderList_of_mem {t : PTree} {ts : List PTree}
    (ht : t ∈ ts) : PTree.order t ≤ PTree.orderList ts := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      rw [PTree.orderList_cons]
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := ih ht
        omega

mutual

/-- Small-tree stage weights lie in the polynomial spaces of the manuscript. -/
theorem stagePolynomial (h : RankOneOrderConditions rk q c r) :
    ∀ t : PTree, PTree.order t ≤ r →
      IsStagePolynomial c (PTree.order t - 1) (stageWeight rk t)
  | .node ts, ht => by
      rw [PTree.order_node] at ht ⊢
      rw [show stageWeight rk (.node ts) = stageWeightList rk ts from funext fun _ => rfl]
      simpa using h.listPolynomial ts (by omega)

theorem listPolynomial (h : RankOneOrderConditions rk q c r) :
    ∀ ts : List PTree, PTree.orderList ts < r →
      IsStagePolynomial c (PTree.orderList ts) (stageWeightList rk ts)
  | [], _ => by
      rw [show stageWeightList rk [] = (fun _ => 1) from funext fun _ => rfl]
      simpa using IsStagePolynomial.const (c := c) (1 : R) 0
  | t :: ts, hts => by
      rw [PTree.orderList_cons] at hts
      have ht := h.stagePolynomial t (by omega)
      have hA := h.closure (PTree.order t - 1) (by have := PTree.order_pos t; omega)
        (stageWeight rk t) ht
      have htail := h.listPolynomial ts (by omega)
      rw [show stageWeightList rk (t :: ts) =
        (fun i => (∑ j, rk.A i j * stageWeight rk t j) * stageWeightList rk ts i)
        from funext fun _ => rfl]
      simpa only [stageWeightList_cons, PTree.orderList_cons,
        Nat.sub_add_cancel (PTree.order_pos t)] using hA.mul htail

end

mutual

/-- The perturbation leaves stage weights unchanged through order `r+1`. -/
theorem stageWeight_perturb_eq (h : RankOneOrderConditions rk q c r) :
    ∀ t : PTree, PTree.order t ≤ r + 1 → ∀ i,
      stageWeight (rankOnePerturb rk q) t i = stageWeight rk t i
  | .node ts, ht, i => by
      rw [stageWeight_node, stageWeight_node]
      apply h.stageWeightList_perturb_eq ts _ i
      intro t hmem
      have := order_le_orderList_of_mem hmem
      rw [PTree.order_node] at ht
      omega

theorem stageWeightList_perturb_eq (h : RankOneOrderConditions rk q c r) :
    ∀ ts : List PTree, (∀ t ∈ ts, PTree.order t ≤ r) → ∀ i,
      stageWeightList (rankOnePerturb rk q) ts i = stageWeightList rk ts i
  | [], _, _ => rfl
  | t :: ts, hts, i => by
      have ht := hts t (by simp)
      have htail : ∀ u ∈ ts, PTree.order u ≤ r := fun u hu => hts u (by simp [hu])
      rw [stageWeightList_cons, stageWeightList_cons,
        h.stageWeightList_perturb_eq ts htail i]
      have heq : (∑ j, (rankOnePerturb rk q).A i j *
          stageWeight (rankOnePerturb rk q) t j) = ∑ j, rk.A i j * stageWeight rk t j := by
        simp_rw [h.stageWeight_perturb_eq t (by omega)]
        exact h.perturb_mul (by have := PTree.order_pos t; omega) (h.stagePolynomial t ht) i
      rw [heq]

end

theorem sum_weightedTranspose (h : RankOneOrderConditions rk q c r) (f g : ι → R) :
    (∑ i, rk.b i * f i * ∑ j, rk.A i j * g j) =
      ∑ j, rk.b j * (∑ i, rankOneTranspose rk q j i * f i) * g j := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  linear_combination -f i * g j * h.weightedTranspose j i

/-- The weighted-transpose cancellation applied to elementary stage weights. -/
theorem weightedStageWeight_perturb_eq (h : RankOneOrderConditions rk q c r) :
    ∀ (t : PTree) (k : ℕ) (f : ι → R), k + PTree.order t ≤ 2 * r + 1 →
      IsStagePolynomial c k f →
      (∑ i, rk.b i * f i * stageWeight (rankOnePerturb rk q) t i) =
        ∑ i, rk.b i * f i * stageWeight rk t i := by
  classical
  suffices H : ∀ (n : ℕ) (t : PTree), PTree.order t = n →
      ∀ (k : ℕ) (f : ι → R), k + PTree.order t ≤ 2 * r + 1 →
        IsStagePolynomial c k f →
        (∑ i, rk.b i * f i * stageWeight (rankOnePerturb rk q) t i) =
          ∑ i, rk.b i * f i * stageWeight rk t i by
    intro t
    exact H (PTree.order t) t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro t hn k f hbound hf
      cases t with
      | node ts =>
          by_cases hsmall : ∀ u ∈ ts, PTree.order u ≤ r
          · simp_rw [stageWeight_node, h.stageWeightList_perturb_eq ts hsmall]
          · push Not at hsmall
            obtain ⟨u, humem, hu⟩ := hsmall
            let us := ts.erase u
            have hperm : ts.Perm (u :: us) := List.perm_cons_erase humem
            have horder := PTree.orderList_perm hperm
            rw [PTree.orderList_cons] at horder
            have hbudget : k + PTree.order u + PTree.orderList us ≤ 2 * r := by
              rw [PTree.order_node, horder] at hbound
              omega
            have huless : PTree.order u < n := by
              rw [PTree.order_node, horder] at hn
              omega
            have htail : ∀ v ∈ us, PTree.order v ≤ r := by
              intro v hv
              have := order_le_orderList_of_mem hv
              omega
            let w : ι → R := fun i => f i * stageWeightList rk us i
            have hw : IsStagePolynomial c (k + PTree.orderList us) w :=
              hf.mul (h.listPolynomial us (by omega))
            have hzero := h.annihilation (k + PTree.orderList us) (by omega) w hw
            have hperturb : ∀ i, (∑ j, (rankOnePerturb rk q).A i j *
                stageWeight (rankOnePerturb rk q) u j) =
                (∑ j, rk.A i j * stageWeight (rankOnePerturb rk q) u j) +
                  q i * (∑ j, rk.b j * q j * stageWeight (rankOnePerturb rk q) u j) := by
              intro i
              simp only [rankOnePerturb, add_mul, Finset.sum_add_distrib]
              simp_rw [mul_assoc, ← Finset.mul_sum]
            have hgoal : (∑ i, rk.b i * w i *
                ∑ j, (rankOnePerturb rk q).A i j * stageWeight (rankOnePerturb rk q) u j) =
                ∑ i, rk.b i * w i * ∑ j, rk.A i j * stageWeight rk u j := by
              simp_rw [hperturb, mul_add, Finset.sum_add_distrib]
              have hterm : (∑ i, rk.b i * w i *
                  (q i * (∑ j, rk.b j * q j * stageWeight (rankOnePerturb rk q) u j))) = 0 := by
                calc
                  _ = (∑ i, rk.b i * q i * w i) *
                      (∑ j, rk.b j * q j * stageWeight (rankOnePerturb rk q) u j) := by
                    rw [Finset.sum_mul]
                    exact Finset.sum_congr rfl fun i _ => by ring
                  _ = 0 := by rw [hzero, zero_mul]
              rw [hterm, add_zero]
              by_cases husmall : PTree.order u ≤ r + 1
              · simp_rw [h.stageWeight_perturb_eq u husmall]
              · rw [h.sum_weightedTranspose w (stageWeight (rankOnePerturb rk q) u),
                  h.sum_weightedTranspose w (stageWeight rk u)]
                exact ih (PTree.order u) huless u rfl (k + PTree.orderList us + 1)
                  (fun j => ∑ i, rankOneTranspose rk q j i * w i) (by omega)
                  (h.transpose_closure (by omega) hw)
            simpa only [stageWeight_node,
              stageWeightList_perm (rankOnePerturb rk q) _ hperm,
              stageWeightList_perm rk _ hperm, stageWeightList_cons,
              h.stageWeightList_perturb_eq us htail, w, mul_assoc, mul_left_comm, mul_comm] using hgoal

/-- A rank-one adjoint perturbation leaves all weights through order `2r+1` unchanged. -/
theorem weight_perturb_eq (h : RankOneOrderConditions rk q c r)
    {t : PTree} (ht : PTree.order t ≤ 2 * r + 1) :
    weight (rankOnePerturb rk q) t = weight rk t := by
  simpa [weight, rankOnePerturb] using
    h.weightedStageWeight_perturb_eq t 0 (fun _ => 1) (by omega)
      (IsStagePolynomial.const (c := c) (1 : R) 0)

/-- The general order lemma, with the adjoint expressed after a stage permutation. -/
theorem hasAntisymOrder [CharZero R] [Invertible (2 : R)]
    (h : RankOneOrderConditions rk q c r) (e : ι ≃ ι)
    (hadj : reindex e (adjointScheme rk) = rankOnePerturb rk q) :
    ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * r + 1) := by
  apply hasAntisymOrder_of_weight_adjoint_eq
  intro t ht
  rw [← weight_reindex e (adjointScheme rk) t, hadj]
  exact h.weight_perturb_eq ht

end RankOneOrderConditions

end BSeries.RungeKutta
