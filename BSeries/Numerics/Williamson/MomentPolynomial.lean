import BSeries.Numerics.Williamson.AreaTableau
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Rat

/-!
# Universal moment polynomials

The area identity gives a constructive version of the moment reduction:
`(m+1) ∫ (∏ Xᵢ) dY = Y ∏ Xᵢ + ∑ᵢ ∫ (∏ⱼ≠ᵢ Xⱼ) d area(Xᵢ,Y)`.
The number of factors decreases in each integral on the right. This is the
polynomial integration-by-parts form of the reduction in Lemma 3 of
`papers/williamson_order_transfer.tex`.
-/

namespace BSeries.WilliamsonMoments

open HopfAlgebras

/-- A rational linear combination of moment monomials. -/
inductive Poly where
  | zero
  | monomial (ts : List PTree)
  | add (p q : Poly)
  | scale (c : ℚ) (p : Poly)

namespace Poly

def eval {R : Type*} [CommRing R] [Algebra ℚ R] (X : PTree → R) : Poly → R
  | .zero => 0
  | .monomial ts => (ts.map X).prod
  | .add p q => eval X p + eval X q
  | .scale c p => (algebraMap ℚ R c) * eval X p

def sum : List Poly → Poly := List.foldr .add .zero

@[simp] theorem eval_sum {R : Type*} [CommRing R] [Algebra ℚ R] (X : PTree → R)
    (ps : List Poly) : eval X (sum ps) = (ps.map (eval X)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [sum, eval] using congrArg (eval X p + ·) ih

/-- A homogeneous expression of classical moment weight `n`. -/
inductive Homogeneous : Poly → ℕ → Prop
  | zero (n) : Homogeneous .zero n
  | monomial (ts) : Homogeneous (.monomial ts) (PTree.orderList ts)
  | add {p q n} : Homogeneous p n → Homogeneous q n → Homogeneous (.add p q) n
  | scale {p n} (c) : Homogeneous p n → Homogeneous (.scale c p) n

theorem homogeneous_sum (ps : List Poly) (n : ℕ)
    (h : ∀ p ∈ ps, Homogeneous p n) : Homogeneous (sum ps) n := by
  induction ps with
  | nil => exact .zero n
  | cons p ps ih =>
      exact .add (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

end Poly

/-- Select one occurrence, retaining every other factor, including repeats. -/
def selections {α : Type*} : List α → List (α × List α)
  | [] => []
  | a :: as => (a, as) :: (selections as).map (fun p => (p.1, a :: p.2))

theorem selections_length {α : Type*} (as : List α) :
    (selections as).length = as.length := by
  induction as <;> simp [selections, *]

theorem selections_perm {α : Type*} {as : List α} {p : α × List α}
    (h : p ∈ selections as) : (p.1 :: p.2).Perm as := by
  induction as generalizing p with
  | nil => simp [selections] at h
  | cons a as ih =>
      simp only [selections, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨q, hq, rfl⟩
      · exact .refl _
      · exact (List.Perm.swap _ _ _).trans ((ih hq).cons a)

theorem selections_rest_length {α : Type*} {as : List α} {p : α × List α}
    (h : p ∈ selections as) : p.2.length + 1 = as.length := by
  simpa using (selections_perm h).length_eq

theorem selections_order {as : List PTree} {p : PTree × List PTree}
    (h : p ∈ selections as) : PTree.order p.1 + PTree.orderList p.2 =
      PTree.orderList as := by
  exact PTree.orderList_perm (selections_perm h)

/-- Differential of a monomial, by Leibniz's rule. -/
def dmonomial {R : Type*} [CommRing R] (X V : PTree → R) : List PTree → R
  | [] => 0
  | t :: ts => V t * (ts.map X).prod + X t * dmonomial X V ts

def Poly.diff {R : Type*} [CommRing R] [Algebra ℚ R] (X V : PTree → R) : Poly → R
  | .zero => 0
  | .monomial ts => dmonomial X V ts
  | .add p q => p.diff X V + q.diff X V
  | .scale c p => (algebraMap ℚ R c) * p.diff X V

@[simp] theorem Poly.diff_sum {R : Type*} [CommRing R] [Algebra ℚ R] (X V : PTree → R)
    (ps : List Poly) : (Poly.sum ps).diff X V = (ps.map (Poly.diff X V)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [Poly.sum, Poly.diff] using congrArg (p.diff X V + ·) ih

theorem selections_diff {R : Type*} [CommRing R] (X V : PTree → R)
    (ts : List PTree) :
    ((selections ts).map (fun p => (p.2.map X).prod * V p.1)).sum =
      dmonomial X V ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [selections, List.map_cons, List.sum_cons, List.map_map,
        dmonomial, Function.comp_def, List.prod_cons]
      simp only [mul_assoc]
      rw [List.sum_map_mul_left, ih]
      ring

theorem selections_product {R : Type*} [CommRing R] (X : PTree → R)
    (ts : List PTree) :
    ((selections ts).map (fun p => (p.2.map X).prod * X p.1)).sum =
      (ts.length : R) * (ts.map X).prod := by
  have heq : ∀ p ∈ selections ts, (p.2.map X).prod * X p.1 = (ts.map X).prod := by
    intro p hp
    simpa [mul_comm] using ((selections_perm hp).map X).prod_eq
  rw [List.map_congr_left heq]
  simp [selections_length, nsmul_eq_mul]

/-- Attach `u` as a new child at the root of `v`. -/
def graft (u v : PTree) : PTree := .node (u :: v.children)

theorem order_graft (u v : PTree) : PTree.order (graft u v) =
    PTree.order u + PTree.order v := by
  cases v
  simp [graft, PTree.order, PTree.orderList, PTree.children]
  omega

/-- Primitive of a moment monomial against one elementary column.
The fuel need only exceed the number of factors. -/
def primitive : ℕ → List PTree → PTree → Poly
  | 0, _, _ => .zero
  | n + 1, ts, v =>
      .scale ((ts.length + 1 : ℚ)⁻¹)
        (.add (.monomial (v :: ts)) (Poly.sum ((selections ts).map fun p =>
          .add (primitive n p.2 (graft p.1 v))
            (.scale (-1) (primitive n p.2 (graft v p.1))))))

private theorem List.sum_map_sub_local {α R : Type*} [AddCommGroup R]
    (xs : List α) (f g : α → R) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, sub_add_sub_comm]

/-- Universal differential identity used for moment reduction. -/
theorem diff_primitive {R : Type*} [CommRing R] [Algebra ℚ R]
    (X V : PTree → R)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (n : ℕ) (ts : List PTree) (v : PTree) (hn : ts.length < n) :
    (primitive n ts v).diff X V = (ts.map X).prod * V v := by
  induction n generalizing ts v with
  | zero => omega
  | succ n ih =>
      have hterms : ∀ p ∈ selections ts,
          (Poly.add (primitive n p.2 (graft p.1 v))
            (.scale (-1) (primitive n p.2 (graft v p.1)))).diff X V =
          (p.2.map X).prod * (X p.1 * V v - X v * V p.1) := by
        intro p hp
        have hlen := selections_rest_length hp
        simp only [Poly.diff]
        rw [ih p.2 _ (by omega), ih p.2 _ (by omega)]
        simp only [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg]
        rw [← mul_sub, harea]
      rw [primitive, Poly.diff, Poly.diff, Poly.diff_sum]
      simp only [List.map_map, Function.comp_def]
      rw [List.map_congr_left hterms]
      have hs :
          ((selections ts).map (fun p =>
            (p.2.map X).prod * (X p.1 * V v - X v * V p.1))).sum =
          (ts.length : R) * (ts.map X).prod * V v - X v * dmonomial X V ts := by
        simp_rw [mul_sub, ← mul_assoc, mul_right_comm _ (X v)]
        rw [List.sum_map_sub_local, List.sum_map_mul_right, List.sum_map_mul_right,
          selections_product, selections_diff]
        ring
      rw [hs]
      dsimp only [Poly.diff, dmonomial]
      have hq : (ts.length + 1 : ℚ)⁻¹ * (ts.length + 1) = 1 :=
        inv_mul_cancel₀ (by positivity)
      have hu : algebraMap ℚ R ((ts.length + 1 : ℚ)⁻¹) * ((ts.length : R) + 1) = 1 := by
        simpa only [map_mul, map_add, map_natCast, map_one] using congrArg (algebraMap ℚ R) hq
      linear_combination hu * (ts.map X).prod * V v

theorem homogeneous_primitive (n : ℕ) (ts : List PTree) (v : PTree) :
    (primitive n ts v).Homogeneous (PTree.orderList ts + PTree.order v) := by
  induction n generalizing ts v with
  | zero => exact .zero _
  | succ n ih =>
      apply Poly.Homogeneous.scale
      apply Poly.Homogeneous.add
      · simpa [PTree.orderList, Nat.add_comm] using Poly.Homogeneous.monomial (v :: ts)
      · apply Poly.homogeneous_sum
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have horder := selections_order hq
        apply Poly.Homogeneous.add
        · convert ih q.2 (graft q.1 v) using 1; rw [order_graft]; omega
        · apply Poly.Homogeneous.scale
          convert ih q.2 (graft v q.1) using 1; rw [order_graft]; omega

namespace Poly

/-- Prefix substitution changes a moment monomial into a stage elementary
vector, by grafting its forest to a new root. -/
def rootEval {R : Type*} [CommRing R] [Algebra ℚ R] (V : PTree → R) : Poly → R
  | .zero => 0
  | .monomial ts => V (.node ts)
  | .add p q => rootEval V p + rootEval V q
  | .scale c p => algebraMap ℚ R c * rootEval V p

def integrateMonomial (ts : List PTree) : Poly → Poly
  | .zero => .zero
  | .monomial us => primitive (ts.length + 1) ts (.node us)
  | .add p q => .add (integrateMonomial ts p) (integrateMonomial ts q)
  | .scale c p => .scale c (integrateMonomial ts p)

/-- Integrate the path polynomial `p` against the stage column obtained
from the prefix polynomial `q`. -/
def integrate : Poly → Poly → Poly
  | .zero, _ => .zero
  | .monomial ts, q => integrateMonomial ts q
  | .add p r, q => .add (integrate p q) (integrate r q)
  | .scale c p, q => .scale c (integrate p q)

theorem diff_integrateMonomial {R : Type*} [CommRing R] [Algebra ℚ R]
    (X V : PTree → R)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (ts : List PTree) (q : Poly) :
    (integrateMonomial ts q).diff X V = (ts.map X).prod * q.rootEval V := by
  induction q with
  | zero => simp [integrateMonomial, diff, rootEval]
  | monomial us => exact diff_primitive X V harea _ _ _ (by omega)
  | add p q hp hq => simp [integrateMonomial, diff, rootEval, hp, hq, mul_add]
  | scale c p hp => simp [integrateMonomial, diff, rootEval, hp, mul_left_comm]

theorem diff_integrate {R : Type*} [CommRing R] [Algebra ℚ R]
    (X V : PTree → R)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (p q : Poly) : (integrate p q).diff X V = p.eval X * q.rootEval V := by
  induction p with
  | zero => simp [integrate, diff, eval]
  | monomial ts => exact diff_integrateMonomial X V harea ts q
  | add p r hp hr => simp [integrate, diff, eval, hp, hr, add_mul]
  | scale c p hp => simp [integrate, diff, eval, hp, mul_assoc]

theorem Homogeneous.integrateMonomial {q : Poly} {n : ℕ}
    (hq : q.Homogeneous n) (ts : List PTree) :
    (integrateMonomial ts q).Homogeneous (PTree.orderList ts + n + 1) := by
  induction hq with
  | zero => exact .zero _
  | monomial us =>
      simpa [Poly.integrateMonomial, PTree.order, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using homogeneous_primitive (ts.length + 1) ts (.node us)
  | add _ _ hp hq => exact .add hp hq
  | scale c _ hp => exact .scale c hp

theorem Homogeneous.integrate {p q : Poly} {m n : ℕ}
    (hp : p.Homogeneous m) (hq : q.Homogeneous n) :
    (Poly.integrate p q).Homogeneous (m + n + 1) := by
  induction hp with
  | zero => exact .zero _
  | monomial ts => exact hq.integrateMonomial ts
  | add _ _ hp hr => exact .add hp hr
  | scale c _ hp => exact .scale c hp

theorem dmonomial_euler {R : Type*} [CommRing R] (X : PTree → R)
    (ts : List PTree) :
    dmonomial X (fun t => (PTree.order t : R) * X t) ts =
      (PTree.orderList ts : R) * (ts.map X).prod := by
  induction ts with
  | nil => simp [dmonomial]
  | cons t ts ih =>
      simp only [dmonomial, ih, PTree.orderList, Nat.cast_add, List.map_cons, List.prod_cons]
      ring

/-- Euler's identity for the moment grading. -/
theorem Homogeneous.euler {R : Type*} [CommRing R] [Algebra ℚ R]
    {p : Poly} {n : ℕ} (hp : p.Homogeneous n) (X : PTree → R) :
    p.diff X (fun t => (PTree.order t : R) * X t) = (n : R) * p.eval X := by
  induction hp with
  | zero => simp [diff, eval]
  | monomial ts => exact dmonomial_euler X ts
  | add _ _ hp hq => simp [diff, eval, hp, hq, mul_add]
  | scale c _ hp => simp [diff, eval, hp, mul_left_comm]

theorem order_le_of_mem {ts : List PTree} {t : PTree} (ht : t ∈ ts) :
    PTree.order t ≤ PTree.orderList ts := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      rcases List.mem_cons.mp ht with rfl | h
      · exact Nat.le_add_right _ _
      · exact le_trans (ih h) (Nat.le_add_left _ _)

/-- Classical moments through the homogeneous weight determine evaluation. -/
theorem Homogeneous.eval_congr {R : Type*} [CommRing R] [Algebra ℚ R]
    {p : Poly} {n : ℕ} (hp : p.Homogeneous n) (X Y : PTree → R)
    (h : ∀ t, PTree.order t ≤ n → X t = Y t) : p.eval X = p.eval Y := by
  induction hp with
  | zero => rfl
  | monomial ts =>
      exact congrArg List.prod (List.map_congr_left fun t ht => h t (order_le_of_mem ht))
  | add _ _ hp hq => simp only [eval, hp h, hq h]
  | scale c _ hp => simp only [eval, hp h]

theorem Homogeneous.eval_zero {R : Type*} [CommRing R] [Algebra ℚ R]
    {p : Poly} {n : ℕ} (hp : p.Homogeneous n) (hn : 0 < n) :
    p.eval (fun _ => (0 : R)) = 0 := by
  induction hp with
  | zero => rfl
  | monomial ts =>
      cases ts with
      | nil => simp at hn
      | cons t ts => simp [eval]
  | add _ _ hp hq => simp [eval, hp hn, hq hn]
  | scale c _ hp => simp [eval, hp hn]

end Poly

end BSeries.WilliamsonMoments
