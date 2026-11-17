import HopfAlgebras.Words.AreaSegment
import Mathlib.Algebra.Polynomial.Coeff
import BSeries.Numerics.Williamson.MomentPolynomial
import BSeries.LieButcher.Order

/-! # Homogeneous moment polynomials for arbitrary ordered trees -/

namespace BSeries.WilliamsonMoments

open HopfAlgebras
open HopfAlgebras.Word.Polynomial
open scoped Polynomial
open Polynomial (C derivative derivative' derivative'_apply derivative_C_mul_X_pow C_mul
  smul_C coeff_C_mul coeff_X_pow)

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
  have h := Poly.derivation_integrate (Polynomial.derivative' : Derivation K K[X] K[X])
    (Word.AreaReduction.segment X V) (Word.AreaReduction.segment_area graft X V harea)
    (orderedForest ts) (orderedTree t)
  have hC := Poly.map_rootEval (Polynomial.CAlgHom : K →ₐ[ℚ] K[X]) V (orderedTree t)
  simp only [Polynomial.derivative'_apply, Word.AreaReduction.derivative_segment] at h
  rw [orderedForest_append_singleton]
  exact h.trans (congrArg _ hC.symm)

variable (K : Type*) [Field K] [CharZero K]

/-- The prescribed classical exact moments. -/
noncomputable def exactMoment (t : PTree) : K := (PTree.treeFactorial t : K)⁻¹

/-- The exact classical moments along the flow: `t ^ |τ| / τ!`. -/
noncomputable def exactPath (t : PTree) : K[X] :=
  C (exactMoment K t) * Polynomial.X ^ PTree.order t

omit [CharZero K] in
theorem exactMoment_prod (ts : List PTree) :
    (ts.map (exactMoment K)).prod = (PTree.treeFactorialList ts : K)⁻¹ := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [exactMoment, ih, mul_comm]

omit [CharZero K] in
theorem exactPath_prod (ts : List PTree) :
    (ts.map (exactPath K)).prod =
      C (ts.map (exactMoment K)).prod * Polynomial.X ^ PTree.orderList ts := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.prod_cons, ih, exactPath, PTree.orderList_cons, C_mul,
        pow_add]
      ring

/-- Differentiating the exact moment of a tree removes its root. -/
theorem derivative_exactPath (t : PTree) :
    derivative (exactPath K t) = (t.children.map (exactPath K)).prod := by
  cases t with
  | node ts =>
      have hn : (PTree.order (.node ts) : K) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (PTree.order_pos (.node ts)))
      rw [exactPath, derivative_C_mul_X_pow, PTree.children, exactPath_prod, exactMoment_prod,
        PTree.order_node, Nat.add_sub_cancel_left]
      congr 2
      simp only [exactMoment, PTree.treeFactorial_node, PTree.order_node, Nat.cast_mul,
        mul_inv_rev] at hn ⊢
      field_simp

/-- The exact flow is closed under signed area. -/
theorem exactPath_area (u v : PTree) :
    derivative' (exactPath K (graft u v)) - derivative' (exactPath K (graft v u)) =
      (derivative' : Derivation K K[X] K[X]).area (exactPath K u) (exactPath K v) := by
  simp [Derivation.area, derivative_exactPath, graft, PTree.children]

theorem rootEval_exactPath (p : Poly) :
    p.rootEval (fun t => derivative (exactPath K t)) = p.eval (exactPath K) := by
  have h : Poly.rootEval (fun t => derivative (exactPath K t)) = Poly.eval (exactPath K) := by
    apply linearMap_ext
    intro ts
    simp [Poly.rootEval, Poly.eval, derivative_exactPath, PTree.children]
  exact LinearMap.congr_fun h p

/-- A homogeneous moment polynomial along the exact flow is a monomial. -/
theorem Poly.Homogeneous.eval_exactPath {p : Poly} {n : ℕ} (hp : p.Homogeneous n) :
    p.eval (exactPath K) = C (p.eval (exactMoment K)) * Polynomial.X ^ n := by
  induction hp with
  | zero => simp
  | monomial ts => simp [Poly.eval, exactPath_prod]
  | add _ _ hp hq => simp only [map_add, hp, hq, add_mul]
  | scale c _ hp => simp only [map_smul, hp, ← smul_C, smul_mul_assoc]

theorem eval_integrate_exact {p q : Poly} {m n : ℕ}
    (hp : p.Homogeneous m) (hq : q.Homogeneous n) :
    (Poly.integrate p q).eval (exactMoment K) =
      p.eval (exactMoment K) * q.eval (exactMoment K) / (m + n + 1 : ℕ) := by
  have hD := Poly.derivation_integrate (derivative' : Derivation K K[X] K[X]) (exactPath K)
    (exactPath_area K) p q
  have hmul : C ((Poly.eval (exactMoment K)) p) * Polynomial.X ^ m *
      (C ((Poly.eval (exactMoment K)) q) * Polynomial.X ^ n) =
      C ((Poly.eval (exactMoment K)) p * (Poly.eval (exactMoment K)) q) *
        Polynomial.X ^ (m + n) := by
    rw [C_mul, pow_add]; ring
  simp only [derivative'_apply] at hD
  rw [rootEval_exactPath, Poly.Homogeneous.eval_exactPath K (hp.integrate hq),
    Poly.Homogeneous.eval_exactPath K hp, Poly.Homogeneous.eval_exactPath K hq,
    derivative_C_mul_X_pow, Nat.add_sub_cancel, hmul] at hD
  have hc := congrArg (fun f : K[X] => f.coeff (m + n)) hD
  simp only [coeff_C_mul, coeff_X_pow, ite_true, mul_one] at hc
  have hn' : ((m + n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + n)
  exact (eq_div_iff hn').mpr hc

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
