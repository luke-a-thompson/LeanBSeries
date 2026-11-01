import BSeries.Numerics.EESWilliamson.NodePeriod
import BSeries.Numerics.EESWilliamson.StagePolynomials
import BSeries.Algebra.PolynomialBidiagonal

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
    obtain hS | ⟨i, hi⟩ := S.eq_empty_or_nonempty
    · simp_all [S]
    apply (Finset.card_le_card_of_injOn (t :=
      {a * c (i.val + 1), -(b * y + d) - a * c (i.val + 1)})
      (fun j : Fin (s + s - 1) => a * c (j.val + 1)) ?_ ?_).trans Finset.card_le_two
    · intro j hj
      have hiq := secondOrder_invariant c a b d hc₀ hc i.val (by have := i.isLt; omega)
      have hjq := secondOrder_invariant c a b d hc₀ hc j.val (by have := j.isLt; omega)
      rw [(Finset.mem_filter.mp hi).2] at hiq
      rw [(Finset.mem_filter.mp hj).2] at hjq
      have h : (a * c (j.val + 1) - a * c (i.val + 1)) *
          (a * c (j.val + 1) + a * c (i.val + 1) + b * y + d) = 0 := by
        linear_combination a * (hjq - hiq)
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · right; linear_combination h
    · intro j hj k hk h
      apply hpairs
      exact Prod.ext ((Finset.mem_filter.mp hj).2.trans
        (Finset.mem_filter.mp hk).2.symm) (mul_left_cancel₀ ha h)
  have hcount := Finset.sum_le_sum (s := nodes) (fun y _ => hfiber y)
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i : Fin (s + s - 1) => c i.val)
    (fun i _ => Finset.mem_image.mpr ⟨⟨i.val, by have := i.isLt; omega⟩,
      Finset.mem_univ _, rfl⟩)] at hcount
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul] at hcount
  change s ≤ nodes.card
  omega

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
  let q := 2 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)
  have h := secondOrder_card_nodes (by omega : 0 < s) c 1 (-2 * q) (q - 1) one_ne_zero hc₀
    (fun k hk => by
      rw [hc ⟨k, by omega⟩, hc ⟨k + 2, hk⟩, hc ⟨k + 1, by omega⟩]
      dsimp [q]
      linear_combination forwardBackward_node_recurrence hs hexp hcons hanti k hk)
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
