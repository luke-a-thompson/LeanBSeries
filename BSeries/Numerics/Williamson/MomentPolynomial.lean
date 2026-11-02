import BSeries.Numerics.Williamson.AreaTableau
import RoughPaths.Signature.AreaReduction
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

abbrev Poly := RoughPaths.AreaReduction.Poly PTree

namespace Poly

export RoughPaths.AreaReduction.Poly (zero monomial add scale eval_sum diff_sum)

abbrev eval {R : Type*} [CommRing R] [Algebra ℚ R] (X : PTree → R) (p : Poly) : R :=
  RoughPaths.AreaReduction.Poly.eval X p

abbrev diff {R : Type*} [CommRing R] [Algebra ℚ R] (X V : PTree → R) (p : Poly) : R :=
  RoughPaths.AreaReduction.Poly.diff X V p

abbrev sum (ps : List Poly) : Poly := RoughPaths.AreaReduction.Poly.sum ps

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

export RoughPaths.AreaReduction (selections selections_perm dmonomial)

theorem selections_order {as : List PTree} {p : PTree × List PTree}
    (h : p ∈ selections as) : PTree.order p.1 + PTree.orderList p.2 =
      PTree.orderList as := by
  exact PTree.orderList_perm (selections_perm h)

/-- Attach `u` as a new child at the root of `v`. -/
def graft (u v : PTree) : PTree := .node (u :: v.children)

theorem order_graft (u v : PTree) : PTree.order (graft u v) =
    PTree.order u + PTree.order v := by
  cases v
  simp [graft, PTree.order, PTree.orderList, PTree.children]
  omega

abbrev primitive (n : ℕ) (ts : List PTree) (v : PTree) : Poly :=
  RoughPaths.AreaReduction.primitive graft n ts v

theorem homogeneous_primitive (n : ℕ) (ts : List PTree) (v : PTree) :
    Poly.Homogeneous (primitive n ts v) (PTree.orderList ts + PTree.order v) := by
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
  | monomial us => exact RoughPaths.AreaReduction.diff_primitive graft X V harea _ _ _ (by omega)
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
  | add _ _ hp hq => simp only [eval, RoughPaths.AreaReduction.Poly.eval, hp h, hq h]
  | scale c _ hp => simp only [eval, RoughPaths.AreaReduction.Poly.eval, hp h]

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
