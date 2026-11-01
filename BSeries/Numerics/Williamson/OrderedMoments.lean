import BSeries.Numerics.Williamson.MomentPolynomial
import BSeries.LieButcher.OrderedExpansion

/-! # Homogeneous moment polynomials for arbitrary ordered trees -/

namespace BSeries.WilliamsonMoments

open HopfAlgebras

def orderedTree : PTree → Poly
  | .node ts => (ts.attach.map fun t => orderedTree t.1).foldl Poly.integrate (.monomial [])
  termination_by t => PTree.order t
  decreasing_by
    have := Poly.order_le_of_mem t.2
    simp only [PTree.order_node]
    omega

def orderedForest (ts : List PTree) : Poly :=
  (ts.map orderedTree).foldl Poly.integrate (.monomial [])

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
    ((ts.map f).foldl Poly.integrate p).Homogeneous (n + PTree.orderList ts) := by
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
    have := Poly.order_le_of_mem ‹t ∈ ts›
    simp only [PTree.order_node]
    omega

theorem homogeneous_orderedForest (ts : List PTree) :
    (orderedForest ts).Homogeneous (PTree.orderList ts) := by
  simpa [orderedForest] using homogeneous_fold orderedTree ts
    (fun t _ => homogeneous_orderedTree t) (.monomial []) 0 (.monomial [])

/-- The prescribed classical exact moments. -/
noncomputable def exactMoment (t : PTree) : ℝ := (PTree.treeFactorial t : ℝ)⁻¹

noncomputable def exactVelocity (t : PTree) : ℝ :=
  (t.children.map exactMoment).prod

theorem exactMoment_prod (ts : List PTree) :
    (ts.map exactMoment).prod = (PTree.treeFactorialList ts : ℝ)⁻¹ := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [exactMoment, ih, mul_comm]

theorem exactVelocity_eq (t : PTree) :
    exactVelocity t = (PTree.order t : ℝ) * exactMoment t := by
  cases t with
  | node ts =>
      have hn : (PTree.order (.node ts) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (PTree.order_pos (.node ts)))
      simp only [exactVelocity, PTree.children, exactMoment_prod, exactMoment,
        PTree.treeFactorial_node, Nat.cast_mul, mul_inv_rev]
      field_simp

theorem exact_area (u v : PTree) :
    exactVelocity (graft u v) - exactVelocity (graft v u) =
      exactMoment u * exactVelocity v - exactMoment v * exactVelocity u := by
  rfl

theorem rootEval_exact (p : Poly) : p.rootEval exactVelocity = p.eval exactMoment := by
  induction p with
  | zero => rfl
  | monomial ts => rfl
  | add p q hp hq => simp [Poly.rootEval, Poly.eval, hp, hq]
  | scale c p hp => simp [Poly.rootEval, Poly.eval, hp]

theorem eval_integrate_exact {p q : Poly} {m n : ℕ}
    (hp : p.Homogeneous m) (hq : q.Homogeneous n) :
    (Poly.integrate p q).eval exactMoment =
      p.eval exactMoment * q.eval exactMoment / (m + n + 1 : ℕ) := by
  have hdiff := Poly.diff_integrate exactMoment exactVelocity exact_area p q
  rw [rootEval_exact] at hdiff
  have heuler := (hp.integrate hq).euler exactMoment
  simp_rw [← exactVelocity_eq] at heuler
  rw [hdiff] at heuler
  have hn' : ((m + n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + n)
  apply (eq_div_iff hn').mpr
  simpa [mul_comm] using heuler.symm

theorem eval_orderedTree_exact (t : PTree) :
    (orderedTree t).eval exactMoment = OrderedExpansion.exactCoeff t.children := by
  cases t with
  | node ts =>
      rw [orderedTree_node]
      change (orderedForest ts).eval exactMoment = OrderedExpansion.exactCoeff ts
      have hchildren : ∀ t ∈ ts,
          (orderedTree t).eval exactMoment = OrderedExpansion.exactCoeff t.children :=
        fun t _ => eval_orderedTree_exact t
      induction ts using List.reverseRecOn with
      | nil => simp [Poly.eval]
      | append_singleton ts t ih =>
          rw [orderedForest_append_singleton,
            eval_integrate_exact (homogeneous_orderedForest ts) (homogeneous_orderedTree t),
            ih (fun u hu => hchildren u (by simp [hu])), hchildren t (by simp),
            OrderedExpansion.exactCoeff_append_singleton]
          congr 1
          have := PTree.order_pos t
          congr 1
          omega
  termination_by PTree.order t
  decreasing_by
    have := Poly.order_le_of_mem ‹t ∈ ts›
    simp only [PTree.order_node]
    omega

/-- Exact-flow specialization of the universal moment polynomial, at every order. -/
theorem eval_orderedForest_exact (ts : List PTree) :
    (orderedForest ts).eval exactMoment = OrderedExpansion.exactCoeff ts := by
  simpa [orderedTree_node, PTree.children] using eval_orderedTree_exact (.node ts)

end BSeries.WilliamsonMoments
