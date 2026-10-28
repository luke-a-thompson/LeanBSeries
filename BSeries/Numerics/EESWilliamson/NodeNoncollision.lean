import BSeries.Numerics.EESWilliamson.NodePeriod
import BSeries.Numerics.EESWilliamson.StagePolynomials
import BSeries.Algebra.PolynomialBidiagonal
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.ComputeDegree

/-!
# Distinct nodes from the second-order recurrence

The full period makes consecutive node pairs distinct. The quadratic invariant permits at most two successors of any node, hence at least `s` distinct composite nodes. A zero Krylov subdiagonal would confine every node to an earlier, smaller set.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Matrix Polynomial
open scoped BigOperators
noncomputable section

/-- The quadratic invariant allows at most two successive pairs above any fixed node. -/
theorem secondOrder_card_nodes {K : Type*} [Field K] [DecidableEq K] {s : ℕ} (hs : 0 < s)
    (c : ℕ → K) (a b d : K) (ha : a ≠ 0) (hc₀ : c 0 = 0)
    (hc : ∀ k, k + 2 < s + s → a * (c k + c (k + 2)) + b * c (k + 1) + d = 0)
    (hpairs : Function.Injective (fun i : Fin (s + s - 1) => (c i.val, c (i.val + 1)))) :
    s ≤ (Finset.univ.image (fun i : Fin (s + s) => c i.val)).card := by
  classical
  let nodes := Finset.univ.image (fun i : Fin (s + s) => c i.val)
  have hfiber (y : K) :
      (Finset.univ.filter (fun i : Fin (s + s - 1) => c i.val = y)).card ≤ 2 := by
    let S := Finset.univ.filter (fun i : Fin (s + s - 1) => c i.val = y)
    let p : K[X] := C a * X ^ 2 + C (b * y + d) * X +
      C (a * y ^ 2 + d * y - (a * c 1 + d) * c 1)
    have hp : p ≠ 0 := by
      intro h
      apply ha
      have h := congrArg (fun p : K[X] => p.coeff 2) h
      norm_num only [p, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at h
      simpa using h
    have hdeg : p.natDegree ≤ 2 := by dsimp [p]; compute_degree
    by_contra! hcard
    apply hp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun i : S => c (i.val.val + 1)) ?_ ?_ ?_)
    · intro i j hij
      apply Subtype.ext
      apply hpairs
      exact Prod.ext ((Finset.mem_filter.mp i.property).2.trans
        (Finset.mem_filter.mp j.property).2.symm) hij
    · intro i
      have h := secondOrder_invariant c a b d hc₀ hc i.val.val (by have := i.val.isLt; omega)
      rw [(Finset.mem_filter.mp i.property).2] at h
      simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination h
    · simpa only [Fintype.card_coe] using hdeg.trans_lt hcard
  by_contra h
  have hn : nodes.card * 2 < (Finset.univ : Finset (Fin (s + s - 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    change ¬ s ≤ nodes.card at h
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun i : Fin (s + s - 1) => c i.val) (t := nodes)
    (fun i _ => Finset.mem_image.mpr ⟨⟨i.val, by have := i.isLt; omega⟩,
      Finset.mem_univ _, rfl⟩) hn
  exact (not_lt_of_ge (hfiber y)) hy

variable {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)]

/-- The composite tableau has at least `s` distinct abscissae. -/
theorem forwardBackward_card_nodes [DecidableEq R] {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    s ≤ (Finset.univ.image rk.forwardBackward.abscissa).card := by
  classical
  have hpairs := (forwardBackward_node_regularity hs hexp hcons hanti).2
  let c : ℕ → R := fun k => if hk : k < s + s then rk.forwardBackward.abscissa ⟨k, hk⟩ else 0
  have hc (i : Fin (s + s)) : c i.val = rk.forwardBackward.abscissa i := by
    simp only [c, dite_eq_left i.isLt]
  have hc₀ : c 0 = 0 := by
    rw [hc ⟨0, by omega⟩]
    exact (isExplicit_forwardBackward rk hexp).abscissa_zero _
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have ha : 1 - 4 * stabilityCoeff rk 3 ≠ 0 := by
    intro h
    apply stabilityCoeff_three_ne_quarter hs hexp hcons hanti
    linear_combination -h / 4
  have h := secondOrder_card_nodes (by omega : 0 < s) c (1 - 4 * stabilityCoeff rk 3)
    (-4 * stabilityCoeff rk 3) (6 * stabilityCoeff rk 3 - 1) ha hc₀
    (fun k hk => by
      rw [hc ⟨k, by omega⟩, hc ⟨k + 2, hk⟩, hc ⟨k + 1, by omega⟩]
      linear_combination forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht k hk)
    (by
      convert hpairs using 1
      funext i
      exact Prod.ext (hc ⟨i.val, by have := i.isLt; omega⟩)
        (hc ⟨i.val + 1, by have := i.isLt; omega⟩))
  simpa only [hc] using h

theorem forwardBackward_krylovSubdiagonal_ne_zero {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (k : Fin (s + s - 1)) (hk : k.val + 1 < s) : t k ≠ 0 := by
  classical
  intro h
  have hle := ht.card_nodes_le_of_eq_zero k h
  have hge := forwardBackward_card_nodes hs hexp hcons hanti
  omega

/-- Nonzero Krylov subdiagonals separate all original stage nodes. -/
theorem abscissa_injective_of_hasAntisymOrder {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) : Function.Injective rk.abscissa := by
  classical
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have hne (i j : Fin s) (hij : i.val < j.val) : rk.abscissa i ≠ rk.abscissa j := by
    have hprod := ht.node_product j.val (by have := j.isLt; omega) (j.castAdd s)
    have hpivot := krylovMatrix_diag_ne_zero (isExplicit_forwardBackward rk hexp)
      (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti) (j.castAdd s)
    have hn : (∏ l : Fin j.val, krylovSubdiagonal t (l.val + 1)) *
        stageWeight rk.forwardBackward (PTree.tallTree j.val) (j.castAdd s) ≠ 0 := by
      apply mul_ne_zero _ hpivot
      apply Finset.prod_ne_zero_iff.mpr
      intro l _
      rw [krylovSubdiagonal_succ t l.val (by have := l.isLt; have := j.isLt; omega)]
      exact forwardBackward_krylovSubdiagonal_ne_zero hs hexp hcons hanti ht _
        (by have := l.isLt; have := j.isLt; change l.val + 1 < s; omega)
    rw [← hprod] at hn
    have h := Finset.prod_ne_zero_iff.mp hn ⟨i.val, hij⟩ (Finset.mem_univ _)
    have hci : rk.forwardBackward.abscissa ⟨i.val, by have := i.isLt; omega⟩ = rk.abscissa i :=
      abscissa_forwardBackward_left rk i
    simp only [abscissa_forwardBackward_left, hci] at h
    exact Ne.symm (sub_ne_zero.mp h)
  exact Function.Injective.of_lt_imp_ne hne

/-- The output eigenvector excludes the output node from all but the last original stage. -/
theorem abscissa_ne_one_of_lt_last {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i : Fin s) (hi : i.val + 1 < s) : rk.abscissa i ≠ 1 := by
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have h := ht ⟨i.val, by have := i.isLt; omega⟩ ((⟨0, by omega⟩ : Fin s).natAdd s)
  simp only [← coeff_stagePolynomial (isExplicit_forwardBackward rk hexp),
    stagePolynomial_forwardBackward_output (by omega) hexp, coeff_stabilityPolynomial hexp,
    abscissa_forwardBackward_right _ hcons, hexp.abscissa_zero, sub_zero] at h
  have hci : rk.forwardBackward.abscissa ⟨i.val, by have := i.isLt; omega⟩ = rk.abscissa i :=
    abscissa_forwardBackward_left rk i
  rw [hci] at h
  intro hi₁
  rw [hi₁, one_mul] at h
  have hz : t ⟨i.val, by have := i.isLt; omega⟩ * stabilityCoeff rk (i.val + 1) = 0 := by
    linear_combination -h
  exact (mul_ne_zero (forwardBackward_krylovSubdiagonal_ne_zero hs hexp hcons hanti ht _ hi)
    ((forwardBackward_node_regularity hs hexp hcons hanti).1 _ (by omega))) hz

end
end BSeries.RungeKutta
