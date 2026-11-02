import BSeries.Numerics.Williamson.AreaTableau
import RoughPaths.Signature.AreaReduction
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Bilinear

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
open HopfAlgebras.Word.Polynomial

noncomputable section

abbrev Poly := RoughPaths.AreaReduction.Poly PTree

namespace Poly

abbrev monomial (ts : List PTree) : Poly := RoughPaths.AreaReduction.Poly.monomial ts
abbrev eval {R : Type*} [CommRing R] [Algebra ℚ R] (X : PTree → R) : Poly →ₗ[ℚ] R :=
  RoughPaths.AreaReduction.Poly.eval X
abbrev diff {R : Type*} [CommRing R] [Algebra ℚ R] (X V : PTree → R) : Poly →ₗ[ℚ] R :=
  RoughPaths.AreaReduction.Poly.diff X V

/-- A homogeneous expression of classical moment weight `n`. -/
inductive Homogeneous : Poly → ℕ → Prop
  | zero (n) : Homogeneous 0 n
  | monomial (ts) : Homogeneous (monomial ts) (PTree.orderList ts)
  | add {p q n} : Homogeneous p n → Homogeneous q n → Homogeneous (p + q) n
  | scale {p n} (c : ℚ) : Homogeneous p n → Homogeneous (c • p) n

theorem homogeneous_sum (ps : List Poly) (n : ℕ)
    (h : ∀ p ∈ ps, Homogeneous p n) : Homogeneous ps.sum n := by
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
        rw [sub_eq_add_neg, ← neg_one_smul ℚ]
        apply Poly.Homogeneous.add
        · convert ih q.2 (graft q.1 v) using 1; rw [order_graft]; omega
        · apply Poly.Homogeneous.scale
          convert ih q.2 (graft v q.1) using 1; rw [order_graft]; omega

namespace Poly

/-- Prefix substitution changes a moment monomial into a stage elementary
vector, by grafting its forest to a new root. -/
def rootEval {R : Type*} [CommRing R] [Algebra ℚ R] (V : PTree → R) : Poly →ₗ[ℚ] R :=
  lift (fun ts => V (.node ts))

@[simp] theorem rootEval_monomial {R : Type*} [CommRing R] [Algebra ℚ R]
    (V : PTree → R) (ts : List PTree) : rootEval V (monomial ts) = V (.node ts) := lift_word _ _

/-- Integrate a moment polynomial against the stage column of another. -/
def integrate : Poly →ₗ[ℚ] Poly →ₗ[ℚ] Poly :=
  lift₂ (fun ts us => primitive (ts.length + 1) ts (.node us))

@[simp] theorem integrate_monomial (ts us : List PTree) :
    integrate (monomial ts) (monomial us) = primitive (ts.length + 1) ts (.node us) :=
  lift₂_word _ _ _

theorem diff_integrate {R : Type*} [CommRing R] [Algebra ℚ R]
    (X V : PTree → R)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u)
    (p q : Poly) : (integrate p q).diff X V = p.eval X * q.rootEval V := by
  have h : integrate.compr₂ (diff X V) =
      (LinearMap.mul ℚ R).compl₁₂ (eval X) (rootEval V) := by
    apply linearMap_ext; intro ts
    apply linearMap_ext; intro us
    simpa [integrate, rootEval, eval] using
      RoughPaths.AreaReduction.diff_primitive graft X V harea _ ts (.node us) (Nat.lt_succ_self _)
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

theorem Homogeneous.integrate {p q : Poly} {m n : ℕ}
    (hp : p.Homogeneous m) (hq : q.Homogeneous n) :
    (Poly.integrate p q).Homogeneous (m + n + 1) := by
  induction hp with
  | zero k => simpa using Homogeneous.zero (k + n + 1)
  | add _ _ hp hr => simpa using Homogeneous.add hp hr
  | scale c _ hp => simpa using Homogeneous.scale c hp
  | monomial ts =>
    induction hq with
    | zero k => simpa using Homogeneous.zero (PTree.orderList ts + k + 1)
    | add _ _ hp hq => simpa using Homogeneous.add hp hq
    | scale c _ hp => simpa using Homogeneous.scale c hp
    | monomial us =>
      simpa [PTree.order, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        homogeneous_primitive (ts.length + 1) ts (.node us)

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
  | zero => simp
  | monomial ts => simpa [diff, eval] using dmonomial_euler X ts
  | add _ _ hp hq => simp [hp, hq, mul_add]
  | scale c _ hp => simp [hp, Algebra.smul_def, mul_left_comm]

theorem order_le_of_mem {ts : List PTree} {t : PTree} (ht : t ∈ ts) :
    PTree.order t ≤ PTree.orderList ts := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      rcases List.mem_cons.mp ht with rfl | h
      · exact Nat.le_add_right _ _
      · exact (ih h).trans (Nat.le_add_left _ _)

/-- Classical moments through the homogeneous weight determine evaluation. -/
theorem Homogeneous.eval_congr {R : Type*} [CommRing R] [Algebra ℚ R]
    {p : Poly} {n : ℕ} (hp : p.Homogeneous n) (X Y : PTree → R)
    (h : ∀ t, PTree.order t ≤ n → X t = Y t) : p.eval X = p.eval Y := by
  induction hp with
  | zero => simp
  | monomial ts =>
      simpa [eval] using congrArg List.prod (List.map_congr_left fun t ht => h t (order_le_of_mem ht))
  | add _ _ hp hq => simp only [map_add, hp h, hq h]
  | scale c _ hp => simp only [map_smul, hp h]

theorem Homogeneous.eval_zero {R : Type*} [CommRing R] [Algebra ℚ R]
    {p : Poly} {n : ℕ} (hp : p.Homogeneous n) (hn : 0 < n) :
    p.eval (fun _ => (0 : R)) = 0 := by
  induction hp with
  | zero => simp
  | monomial ts =>
      cases ts with
      | nil => simp at hn
      | cons t ts => simp [eval]
  | add _ _ hp hq => simp [hp hn, hq hn]
  | scale c _ hp => simp [hp hn]

end Poly

end
end BSeries.WilliamsonMoments
