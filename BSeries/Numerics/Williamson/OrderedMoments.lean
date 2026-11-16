import HopfAlgebras.Words.AreaSegment
import BSeries.Numerics.Williamson.MomentPolynomial
import BSeries.LieButcher.Order

/-! # Homogeneous moment polynomials for arbitrary ordered trees -/

namespace BSeries.WilliamsonMoments

open HopfAlgebras
open HopfAlgebras.Word.Polynomial

noncomputable section

def orderedTree : PTree → Poly
  | .node ts => (ts.attach.map fun t => orderedTree t.1).foldl (fun p q => Poly.integrate p q) (.monomial [])
  termination_by t => PTree.order t
  decreasing_by
    have := PTree.order_le_orderList_of_mem t.2
    simp only [PTree.order_node]
    omega

def orderedForest (ts : List PTree) : Poly :=
  (ts.map orderedTree).foldl (fun p q => Poly.integrate p q) (.monomial [])

theorem orderedTree_node (ts : List PTree) : orderedTree (.node ts) = orderedForest ts := by
  rw [orderedTree, orderedForest, List.attach_map_val]

theorem orderedTree_eq (t : PTree) : orderedTree t = orderedForest t.children := by
  cases t
  exact orderedTree_node _

@[simp] theorem orderedForest_nil : orderedForest [] = .monomial [] := rfl

theorem orderedForest_append_singleton (ts : List PTree) (t : PTree) :
    orderedForest (ts ++ [t]) = Poly.integrate (orderedForest ts) (orderedTree t) := by
  simp [orderedForest]

private theorem homogeneous_fold (f : PTree → Poly) (ts : List PTree)
    (hf : ∀ t ∈ ts, (f t).Homogeneous (PTree.order t - 1))
    (p : Poly) (n : ℕ) (hp : p.Homogeneous n) :
    ((ts.map f).foldl (fun p q => Poly.integrate p q) p).Homogeneous (n + PTree.orderList ts) := by
  induction ts generalizing p n with
  | nil => simpa using hp
  | cons t ts ih =>
      have ht := hf t (by simp)
      have hpos := PTree.order_pos t
      have hp' : (Poly.integrate p (f t)).Homogeneous (n + PTree.order t) := by
        convert hp.integrate ht using 1; omega
      simpa [PTree.orderList, Nat.add_assoc] using
        ih (fun u hu => hf u (by simp [hu])) _ _ hp'

theorem homogeneous_orderedTree (t : PTree) :
    (orderedTree t).Homogeneous (PTree.order t - 1) := by
  cases t with
  | node ts =>
      rw [orderedTree_node, orderedForest]
      simpa [PTree.order] using homogeneous_fold orderedTree ts
        (fun t _ => homogeneous_orderedTree t) (.monomial []) 0 (.monomial [])
  termination_by PTree.order t
  decreasing_by
    have := PTree.order_le_orderList_of_mem ‹t ∈ ts›
    simp only [PTree.order_node]
    omega

theorem homogeneous_orderedForest (ts : List PTree) :
    (orderedForest ts).Homogeneous (PTree.orderList ts) := by
  simpa [orderedForest] using homogeneous_fold orderedTree ts
    (fun t _ => homogeneous_orderedTree t) (.monomial []) 0 (.monomial [])

/-- **Chen's identity for the ordered moment polynomials** on the straight
segment from `X` to `X + V`, whenever `(X, V)` satisfies the area identity. -/
theorem eval_orderedForest_add {K : Type*} [Field K] [CharZero K] (X V : PTree → K)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (ts : List PTree) :
    (orderedForest ts).eval (fun t => X t + V t) =
      ∑ j ∈ Finset.range (ts.length + 1),
        (orderedForest (ts.take j)).eval X * (((ts.drop j).length.factorial : K))⁻¹ *
          ((ts.drop j).map fun t => (orderedTree t).rootEval V).prod := by
  refine Word.AreaReduction.eval_segment X V orderedForest
    (fun t => (orderedTree t).rootEval V) orderedForest_nil (fun ts t => ?_) ts
  have h := Poly.diff_integrate (Word.AreaReduction.segment X V) (fun a => Polynomial.C (V a))
    (Word.AreaReduction.segment_area graft X V harea) (orderedForest ts) (orderedTree t)
  have hC := Poly.map_rootEval (Polynomial.CAlgHom : K →ₐ[ℚ] Polynomial K) V (orderedTree t)
  rw [orderedForest_append_singleton]
  exact h.trans (congrArg _ hC.symm)

variable (K : Type*) [Field K] [CharZero K]

/-- The prescribed classical exact moments. -/
noncomputable def exactMoment (t : PTree) : K := (PTree.treeFactorial t : K)⁻¹

noncomputable def exactVelocity (t : PTree) : K :=
  (t.children.map (exactMoment K)).prod

theorem exactMoment_prod (ts : List PTree) :
    (ts.map (exactMoment K)).prod = (PTree.treeFactorialList ts : K)⁻¹ := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [exactMoment, ih, mul_comm]

theorem exactVelocity_eq (t : PTree) :
    exactVelocity K t = (PTree.order t : K) * exactMoment K t := by
  cases t with
  | node ts =>
      have hn : (PTree.order (.node ts) : K) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (PTree.order_pos (.node ts)))
      simp only [exactVelocity, PTree.children, exactMoment_prod K, exactMoment,
        PTree.treeFactorial_node, Nat.cast_mul, mul_inv_rev]
      field_simp

theorem exact_area (u v : PTree) :
    exactVelocity K (graft u v) - exactVelocity K (graft v u) =
      exactMoment K u * exactVelocity K v - exactMoment K v * exactVelocity K u := by
  simp [exactVelocity, graft, PTree.children]

theorem rootEval_exact (p : Poly) : p.rootEval (exactVelocity K) = p.eval (exactMoment K) := by
  have h : Poly.rootEval (exactVelocity K) = Poly.eval (exactMoment K) := by
    apply linearMap_ext
    intro ts
    simp [Poly.rootEval, Poly.eval, exactVelocity, PTree.children]
  exact LinearMap.congr_fun h p

theorem eval_integrate_exact {p q : Poly} {m n : ℕ}
    (hp : p.Homogeneous m) (hq : q.Homogeneous n) :
    (Poly.integrate p q).eval (exactMoment K) =
      p.eval (exactMoment K) * q.eval (exactMoment K) / (m + n + 1 : ℕ) := by
  have hdiff := Poly.diff_integrate (exactMoment K) (exactVelocity K) (exact_area K) p q
  rw [rootEval_exact K] at hdiff
  have heuler := (hp.integrate hq).euler (exactMoment K)
  simp_rw [← exactVelocity_eq K] at heuler
  rw [hdiff] at heuler
  have hn' : ((m + n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + n)
  apply (eq_div_iff hn').mpr
  simpa [mul_comm] using heuler.symm

theorem eval_orderedTree_exact (t : PTree) :
    (orderedTree t).eval (exactMoment K) = LSSeries.exact K t.children := by
  cases t with
  | node ts =>
      rw [orderedTree_node]
      change (orderedForest ts).eval (exactMoment K) = LSSeries.exact K ts
      have hchildren : ∀ t ∈ ts,
          (orderedTree t).eval (exactMoment K) = LSSeries.exact K t.children :=
        fun t _ => eval_orderedTree_exact t
      induction ts using List.reverseRecOn with
      | nil => simp [Poly.eval]
      | append_singleton ts t ih =>
          rw [orderedForest_append_singleton,
            eval_integrate_exact K (homogeneous_orderedForest ts) (homogeneous_orderedTree t),
            ih (fun u hu => hchildren u (by simp [hu])), hchildren t (by simp),
            LSSeries.exact_append_singleton]
          congr 1
          have := PTree.order_pos t
          congr 1
          omega
  termination_by PTree.order t
  decreasing_by
    have := PTree.order_le_orderList_of_mem ‹t ∈ ts›
    simp only [PTree.order_node]
    omega

/-- Exact-flow specialization of the universal moment polynomial, at every order. -/
theorem eval_orderedForest_exact (ts : List PTree) :
    (orderedForest ts).eval (exactMoment K) = LSSeries.exact K ts := by
  simpa [orderedTree_node, PTree.children] using eval_orderedTree_exact K (.node ts)

end
end BSeries.WilliamsonMoments
