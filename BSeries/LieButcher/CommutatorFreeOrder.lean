/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.LieButcher.Series
import BSeries.Numerics.EES25

/-!
# Lie–Butcher characters of 2N commutator-free methods

The Bazavov lift of a Williamson 2N low-storage scheme advances by
composing exponentials `exp(V_e)` with `V_e = Σ_{i} β_{e,i} K_i`, where
`K_i = ξ(Y_i)` is the vector field frozen at the `i`-th stage point. Its
Lie–Butcher character on planar forests is built by Owren's pseudo-stage
substitution recursion (arXiv:2509.20599, Appendix E.2; Owren, *Order
conditions for commutator-free Lie group methods*, Theorem 2.5):

* the flow character after `e + 1` exponentials splits over
  **deconcatenations** of the forest — the frozen exponential composes by
  operator concatenation —

  `u_{e+1}(ω) = Σ_{ω = ω₁ω₂} u_e(ω₁) ⋅ exp(V_e)(ω₂)`,

  with the shuffle-symmetric single-exponential values
  `exp(V)(ω₂) = (1/|ω₂|!) ∏_{τ ∈ ω₂} V(τ)`;
* the slope characters carry the stage dependence by substitution:
  `K_i(τ) = u_i(children τ)`, the `i`-th stage flow character applied to
  the branches of `τ`.

The method character is `ϕ = u_s`. We formalise the planar order and
antisymmetric order conditions of arXiv:2509.20599, Theorem E.1, and
machine-check them for the concrete `CF-EES(2,5;1/4)` integrator,
cross-validating the character values against Table 6 of the paper.
-/

namespace BSeries

open HopfAlgebras

universe u

namespace LSSeries

variable {R : Type u}

/-- An LB character has **planar order** `p` if it matches the exact-flow
coefficients `1/τ!` on every planar tree of order at most `p`
(arXiv:2509.20599, Theorem E.1(1)). -/
def HasPlanarOrder [Field R] (φ : LSSeries R) (p : ℕ) : Prop :=
  ∀ τ : PTree, PTree.order τ ≤ p →
    φ [τ] = ((PTree.treeFactorial τ : R))⁻¹

/-- The **symmetric defect** of an LB character: the Grossman–Larson
composition of the grading-signed character with the character itself —
the LB character of the roundtrip `Φ_{-h} ∘ Φ_h`
(arXiv:2509.20599, Theorem E.1(2)). -/
def symmetricDefect [Ring R] (φ : LSSeries R) : LSSeries R :=
  PlanarForest.mkwConvolution
    (fun ω => (-1 : R) ^ PTree.orderList ω * φ ω) φ

/-- An LB character has **antisymmetric order** `m` if its symmetric
defect vanishes on every planar tree of order at most `m`: the roundtrip
`Φ_{-h} ∘ Φ_h` recovers the identity to order `m`. -/
def HasPlanarAntisymOrder [Ring R] (φ : LSSeries R) (m : ℕ) : Prop :=
  ∀ τ : PTree, PTree.order τ ≤ m → symmetricDefect φ [τ] = 0

end LSSeries

namespace RungeKutta

namespace LowStorage

variable {R : Type u}

private theorem order_le_orderList_of_mem :
    ∀ {ts : List PTree} {t : PTree}, t ∈ ts →
      PTree.order t ≤ PTree.orderList ts := by
  intro ts
  induction ts with
  | nil => intro t h; cases h
  | cons a ts ih =>
      intro t h
      rw [PTree.orderList_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_add_right _ _
      · exact le_trans (ih h) (Nat.le_add_left _ _)

private theorem orderList_take_le (ω : List PTree) (j : ℕ) :
    PTree.orderList (ω.take j) ≤ PTree.orderList ω := by
  conv_rhs => rw [← List.take_append_drop j ω]
  rw [PTree.orderList_append]
  exact Nat.le_add_right _ _

private theorem orderList_drop_le (ω : List PTree) (j : ℕ) :
    PTree.orderList (ω.drop j) ≤ PTree.orderList ω := by
  conv_rhs => rw [← List.take_append_drop j ω]
  rw [PTree.orderList_append]
  exact Nat.le_add_left _ _

/-- The Lie–Butcher flow character `u_e` after `e` exponentials of the
Bazavov commutator-free lift (Owren's substitution recursion;
arXiv:2509.20599, Appendix E.2, equation (18)): `u_0 = ε` and

  `u_{e+1}(ω) = Σ_{ω = ω₁ω₂} u_e(ω₁) ⋅ (1/|ω₂|!) ∏_{τ ∈ ω₂} V_e(τ)`,

where `V_e(τ) = Σ_i β_{e,i} u_i(children τ)` combines the vector fields
frozen at the stage points. -/
def flowChar [Field R] {s : ℕ} (ls : LowStorage s R) :
    ℕ → PlanarForest → R
  | 0, ω => if ω = [] then 1 else 0
  | e + 1, ω =>
      ((List.range (ω.length + 1)).map fun j =>
        flowChar ls e (ω.take j) *
          (((Nat.factorial (ω.drop j).length : R))⁻¹ *
            (((ω.drop j).attach.map fun τ =>
              ((List.range s).map fun i =>
                (if h : e < s ∧ i < s then
                  ls.beta ⟨e, h.1⟩ ⟨i, h.2⟩ else 0) *
                  flowChar ls i (PTree.children τ.1)).sum).prod))).sum
  termination_by e ω => (PTree.orderList ω, e)
  decreasing_by
    · rcases Nat.lt_or_ge (PTree.orderList (ω.take j))
        (PTree.orderList ω) with h | h
      · exact Prod.Lex.left _ _ h
      · have heq : PTree.orderList (ω.take j) = PTree.orderList ω :=
          le_antisymm (orderList_take_le ω j) h
        rw [heq]
        exact Prod.Lex.right _ (by omega)
    · have h1 : PTree.order τ.1 ≤ PTree.orderList (ω.drop j) :=
        order_le_orderList_of_mem τ.2
      have h2 := orderList_drop_le ω j
      have h3 := PTree.order_eq_one_add_orderList_children τ.1
      exact Prod.Lex.left _ _ (by omega)

/-- The Lie–Butcher character of the commutator-free method induced by a
low-storage scheme: the flow character after all `s` exponentials
(arXiv:2509.20599, Appendix E.2, equation (19)). -/
def methodChar [Field R] {s : ℕ} (ls : LowStorage s R) : LSSeries R :=
  flowChar ls s

/-- Every flow character takes the value one on the empty forest. -/
@[simp]
theorem flowChar_nil [Field R] {s : ℕ} (ls : LowStorage s R) :
    ∀ e, flowChar ls e [] = 1
  | 0 => by rw [flowChar]; simp
  | e + 1 => by
      rw [flowChar]
      simp only [List.length_nil, show List.range 1 = [0] from rfl,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      dsimp only [List.drop, List.attach, List.attachWith, List.pmap]
      simp [flowChar_nil ls e]

@[simp]
theorem methodChar_nil [Field R] {s : ℕ} (ls : LowStorage s R) :
    methodChar ls [] = 1 :=
  flowChar_nil ls s

theorem list_sum_range_eq {M : Type*} [AddCommMonoid M] :
    ∀ (n : ℕ) (f : ℕ → M),
      ((List.range n).map f).sum = ∑ m ∈ Finset.range n, f m
  | 0, f => rfl
  | n + 1, f => by
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, list_sum_range_eq n f]
      simp

/-- The flow character on the single-node forest accumulates the row sums
of the slope weights: `u_e([•]) = Σ_{m<e} Σ_i β_{m,i}`. -/
theorem flowChar_bullet [Field R] {s : ℕ} (ls : LowStorage s R) :
    ∀ e, flowChar ls e [PTree.bullet] =
      ((List.range e).map fun m =>
        ((List.range s).map fun i =>
          if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩
          else 0).sum).sum
  | 0 => by
      rw [flowChar]
      simp
  | e + 1 => by
      rw [flowChar]
      have h2 : ([PTree.bullet] : PlanarForest).length + 1 = 2 := rfl
      rw [h2, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.take_zero, List.drop_zero, List.take_succ_cons, List.take_nil,
        List.drop_succ_cons, List.drop_nil, List.length_cons,
        List.length_nil, List.attach_nil, flowChar_nil ls]
      dsimp only [List.drop, List.attach, List.attachWith, List.pmap]
      rw [flowChar_bullet ls e]
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [List.attach_cons, PTree.children, PTree.bullet, Nat.factorial]
      ring

/-- **Consistency of the Lie–Butcher character**: on the single-node tree
the method character of the commutator-free lift equals the sum of the
induced quadrature weights `Σⱼ bⱼ`. -/
theorem methodChar_bullet [Field R] {s : ℕ} (ls : LowStorage s R) :
    methodChar ls [PTree.bullet] = ∑ j, (toRK ls).b j := by
  rw [methodChar, flowChar_bullet, list_sum_range_eq]
  have h1 : ∀ m ∈ Finset.range s,
      ((List.range s).map fun i =>
        if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0).sum =
      ∑ i ∈ Finset.range s,
        if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0 :=
    fun m _ => list_sum_range_eq s _
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ j, (toRK ls).b j = ∑ m, ls.beta m j := fun j => toRK_b ls j
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ m ∈ Finset.range s,
    if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0) s]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun m =>
    if h : m < s ∧ (i : ℕ) < s then ls.beta ⟨m, h.1⟩ ⟨(i : ℕ), h.2⟩ else 0) s]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dif_pos ⟨m.isLt, i.isLt⟩]

/-! ### The flow character on trees of order at most two

In general the method character reproduces the Runge–Kutta elementary
weights of the induced tableau on the bullet and the two-chain, which
yields the planar order-two condition for a whole family at once. -/

private theorem sum_range_dite_eq_sum_univ {M : Type*} [AddCommMonoid M]
    {s : ℕ} (f : Fin s → M) :
    (∑ m ∈ Finset.range s, if h : m < s then f ⟨m, h⟩ else 0) = ∑ m, f m := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => if h : m < s then f ⟨m, h⟩
    else 0) s]
  exact Finset.sum_congr rfl fun m _ => by
    rw [dif_pos m.isLt]

private theorem sum_Iio_fin_eq_sum_range {M : Type*} [AddCommMonoid M]
    {s : ℕ} (p : Fin s) (f : Fin s → M) :
    ∑ m ∈ Finset.Iio p, f m =
      ∑ m ∈ Finset.range (p : ℕ), if h : m < s then f ⟨m, h⟩ else 0 := by
  refine Finset.sum_bij'
    (i := fun (a : Fin s) (_ : a ∈ Finset.Iio p) => (a : ℕ))
    (j := fun (m : ℕ) (hm : m ∈ Finset.range (p : ℕ)) =>
      (⟨m, lt_trans (Finset.mem_range.mp hm) p.isLt⟩ : Fin s))
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range]
    exact Fin.lt_def.mp (Finset.mem_Iio.mp ha)
  · intro m hm
    rw [Finset.mem_Iio]
    exact Fin.lt_def.mpr (Finset.mem_range.mp hm)
  · intro a _
    exact Fin.ext rfl
  · intro m _
    rfl
  · intro a _
    rw [dif_pos a.isLt]

private theorem toRK_A_eq_range [Field R] {s : ℕ} (ls : LowStorage s R)
    (i j : Fin s) :
    (toRK ls).A i j = ∑ m ∈ Finset.range (i : ℕ),
      if h : m < s then ls.beta ⟨m, h⟩ j else 0 := by
  rw [toRK_A]
  exact sum_Iio_fin_eq_sum_range i fun m => ls.beta m j

/-- The flow character on the single bullet is the partial abscissa: for
`i < s`, `u_i([•]) = c_i`, the `i`-th row sum of the induced tableau. -/
theorem flowChar_bullet_eq_abscissa [Field R] {s : ℕ} (ls : LowStorage s R)
    (i : Fin s) :
    flowChar ls (i : ℕ) [PTree.bullet] = abscissa (toRK ls) i := by
  rw [flowChar_bullet, list_sum_range_eq, abscissa,
    Finset.sum_congr rfl fun j _ => toRK_A_eq_range ls i j,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [list_sum_range_eq]
  by_cases hm : m < s
  · rw [show (∑ j ∈ Finset.range s, if h : m < s ∧ j < s then
        ls.beta ⟨m, h.1⟩ ⟨j, h.2⟩ else 0) =
        ∑ j ∈ Finset.range s, if h : j < s then ls.beta ⟨m, hm⟩ ⟨j, h⟩
          else 0 from
      Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_range] at hj
        rw [dif_pos ⟨hm, hj⟩, dif_pos hj]]
    rw [sum_range_dite_eq_sum_univ fun j => ls.beta ⟨m, hm⟩ j]
    exact (Finset.sum_congr rfl fun j _ => by rw [dif_pos hm]).symm
  · rw [Finset.sum_eq_zero fun j _ => dif_neg fun hc => hm hc.1,
      Finset.sum_eq_zero fun j _ => dif_neg hm]

/-- The flow character on the two-chain accumulates the slope weights
against the bullet values. -/
theorem flowChar_chain2 [Field R] {s : ℕ} (ls : LowStorage s R) :
    ∀ e, flowChar ls e [PTree.chain2] =
      ((List.range e).map fun m =>
        ((List.range s).map fun i =>
          (if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0) *
            flowChar ls i [PTree.bullet]).sum).sum
  | 0 => by
      rw [flowChar]
      simp
  | e + 1 => by
      rw [flowChar]
      have h2 : ([PTree.chain2] : PlanarForest).length + 1 = 2 := rfl
      rw [h2, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.take_zero, List.drop_zero, List.take_succ_cons, List.take_nil,
        List.drop_succ_cons, List.drop_nil, List.length_cons,
        List.length_nil, List.attach_nil, flowChar_nil ls]
      dsimp only [List.drop, List.attach, List.attachWith, List.pmap]
      rw [flowChar_chain2 ls e]
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [List.attach_cons, PTree.children, PTree.chain2, Nat.factorial]
      ring

/-- **The Lie–Butcher character matches the Runge–Kutta weight on the
two-chain**: `ϕ(chain₂) = Σᵢ bᵢ cᵢ` for the induced tableau. -/
theorem methodChar_chain2 [Field R] {s : ℕ} (ls : LowStorage s R) :
    methodChar ls [PTree.chain2] =
      ∑ i, (toRK ls).b i * abscissa (toRK ls) i := by
  rw [methodChar, flowChar_chain2, list_sum_range_eq]
  rw [Finset.sum_congr rfl fun m _ => list_sum_range_eq s _]
  rw [Finset.sum_comm]
  have h1 : ∀ i ∈ Finset.range s,
      (∑ m ∈ Finset.range s,
        (if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0) *
          flowChar ls i [PTree.bullet]) =
      if h : i < s then
        (∑ m, ls.beta m ⟨i, h⟩) * abscissa (toRK ls) ⟨i, h⟩ else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [dif_pos hi, Finset.sum_mul]
    have h2 : ∀ m ∈ Finset.range s,
        (if h : m < s ∧ i < s then ls.beta ⟨m, h.1⟩ ⟨i, h.2⟩ else 0) *
          flowChar ls i [PTree.bullet] =
        (if h : m < s then ls.beta ⟨m, h⟩ ⟨i, hi⟩ else 0) *
          abscissa (toRK ls) ⟨i, hi⟩ := by
      intro m _
      rw [flowChar_bullet_eq_abscissa ls ⟨i, hi⟩]
      congr 1
      by_cases hm : m < s
      · rw [dif_pos ⟨hm, hi⟩, dif_pos hm]
      · rw [dif_neg (fun hc => hm hc.1), dif_neg hm]
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul,
      sum_range_dite_eq_sum_univ fun m => ls.beta m ⟨i, hi⟩]
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl h1,
    sum_range_dite_eq_sum_univ fun i =>
      (∑ m, ls.beta m i) * abscissa (toRK ls) i]
  exact Finset.sum_congr rfl fun i _ => by rw [← toRK_b]


/-! ### A memoised evaluator

`flowChar` recomputes stage characters exponentially often along deep
trees. For machine-checked order conditions we use an equivalent
evaluator that annotates each tree once with its slope values
`[u_0(children τ), …, u_{s-1}(children τ)]` and never re-descends into
trees, making character evaluation polynomial in the forest order. -/

/-- The slope values of a tree, as data:
`trueSlopes τ = [u_0(children τ), …, u_{s-1}(children τ)]`. -/
def trueSlopes [Field R] {s : ℕ} (ls : LowStorage s R) (τ : PTree) :
    List R :=
  (List.range s).map fun i => flowChar ls i (PTree.children τ)

/-- The flow character evaluated on a forest of precomputed slope-value
lists: the recursion never re-enters the trees. -/
def flowCharAnn [Field R] {s : ℕ} (ls : LowStorage s R) :
    ℕ → List (List R) → R
  | 0, vs => if vs = [] then 1 else 0
  | e + 1, vs =>
      ((List.range (vs.length + 1)).map fun j =>
        flowCharAnn ls e (vs.take j) *
          (((Nat.factorial (vs.drop j).length : R))⁻¹ *
            (((vs.drop j).map fun v =>
              ((List.range s).map fun i =>
                (if h : e < s ∧ i < s then
                  ls.beta ⟨e, h.1⟩ ⟨i, h.2⟩ else 0) *
                  v.getD i 0).sum).prod))).sum

/-- The memoised slope annotation: each subtree's slope list is computed
exactly once. -/
def slopeList [Field R] {s : ℕ} (ls : LowStorage s R) : PTree → List R
  | .node ts =>
      let cs := ts.attach.map fun τ => slopeList ls τ.1
      (List.range s).map fun i => flowCharAnn ls i cs
  termination_by τ => PTree.order τ
  decreasing_by
    have h1 : PTree.order τ.1 ≤ PTree.orderList ts :=
      order_le_orderList_of_mem τ.2
    have h2 : PTree.order (PTree.node ts) = 1 + PTree.orderList ts :=
      PTree.order_eq_one_add_orderList_children _
    omega

/-- The memoised method character. -/
def fastMethodChar [Field R] {s : ℕ} (ls : LowStorage s R)
    (ω : PlanarForest) : R :=
  flowCharAnn ls s (ω.map (slopeList ls))

private theorem getD_map_range {M : Type*} [Zero M] (g : ℕ → M)
    {s i : ℕ} (h : i < s) : ((List.range s).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private theorem flowCharAnn_map_trueSlopes [Field R] {s : ℕ}
    (ls : LowStorage s R) :
    ∀ (e : ℕ) (ω : PlanarForest),
      flowCharAnn ls e (ω.map (trueSlopes ls)) = flowChar ls e ω
  | 0, ω => by
      rw [flowCharAnn, flowChar]
      simp [List.map_eq_nil_iff]
  | e + 1, ω => by
      rw [flowCharAnn, flowChar, List.length_map]
      refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
      rw [← List.map_take, flowCharAnn_map_trueSlopes ls e (ω.take j)]
      congr 1
      rw [← List.map_drop, List.length_map]
      congr 1
      rw [List.map_map,
        List.attach_map_val (l := ω.drop j) (f := fun τ =>
          ((List.range s).map fun i =>
            (if h : e < s ∧ i < s then ls.beta ⟨e, h.1⟩ ⟨i, h.2⟩
              else 0) * flowChar ls i (PTree.children τ)).sum)]
      refine congrArg List.prod (List.map_congr_left fun τ _ => ?_)
      refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
      rw [List.mem_range] at hi
      simp only [trueSlopes]
      rw [getD_map_range _ hi]
  termination_by e _ => e

private theorem slopeList_eq_trueSlopes [Field R] {s : ℕ}
    (ls : LowStorage s R) : ∀ τ : PTree, slopeList ls τ = trueSlopes ls τ
  | .node ts => by
      rw [slopeList, trueSlopes]
      refine List.map_congr_left fun i _ => ?_
      have hmap : ts.attach.map (fun τ => slopeList ls τ.1) =
          ts.map (trueSlopes ls) := by
        rw [← List.attach_map_val (l := ts) (f := trueSlopes ls)]
        refine List.map_congr_left fun τ _ => ?_
        exact slopeList_eq_trueSlopes ls τ.1
      rw [hmap, flowCharAnn_map_trueSlopes]
      rfl
  termination_by τ => PTree.order τ
  decreasing_by
    have h1 : PTree.order τ.1 ≤ PTree.orderList ts :=
      order_le_orderList_of_mem τ.2
    have h2 : PTree.order (PTree.node ts) = 1 + PTree.orderList ts :=
      PTree.order_eq_one_add_orderList_children _
    omega

/-- **The memoised evaluator computes the method character.** All
machine-checked order conditions evaluate `fastMethodChar` instead of
the exponential-time `methodChar` recursion. -/
theorem fastMethodChar_eq [Field R] {s : ℕ} (ls : LowStorage s R) :
    fastMethodChar ls = methodChar ls := by
  funext ω
  rw [fastMethodChar, methodChar,
    List.map_congr_left fun τ _ => slopeList_eq_trueSlopes ls τ,
    flowCharAnn_map_trueSlopes]

end LowStorage

/-! ### Planar order two from the induced tableau -/

open LowStorage in
/-- **Planar order two from the induced tableau weights**: if the induced
Butcher tableau of a low-storage scheme is consistent (`Σⱼ bⱼ = 1`) and
satisfies the classical order-two condition (`Σᵢ bᵢcᵢ = 1/2`), then the
commutator-free lift has planar order two on any homogeneous space. -/
theorem hasPlanarOrder_two_of_toRK {R : Type u} [Field R] {s : ℕ} (ls : LowStorage s R)
    (h1 : ∑ j, (toRK ls).b j = 1)
    (h2 : ∑ i, (toRK ls).b i * abscissa (toRK ls) i = 1 / 2) :
    LSSeries.HasPlanarOrder (methodChar ls) 2 := by
  intro τ hτ
  have hpos := PTree.order_pos τ
  have hcases : PTree.order τ = 1 ∨ PTree.order τ = 2 := by omega
  rcases hcases with h | h
  · rw [(PTree.order_eq_one_iff τ).mp h, methodChar_bullet, h1,
      show PTree.treeFactorial PTree.bullet = 1 from rfl]
    norm_num
  · rw [(PTree.order_eq_two_iff τ).mp h, methodChar_chain2, h2,
      show PTree.treeFactorial PTree.chain2 = 2 from rfl]
    norm_num

open LowStorage in
/-- **`CF-EES(2,5;x)` has planar order two for every admissible parameter**
(arXiv:2509.20599, Theorem E.1(1) in full generality): the Lie–Butcher
character of the commutator-free lift of `EES(2,5;x)` matches the exact
flow on all planar trees of order at most two, over any field of
characteristic `≠ 2` and any `x ∉ {1, ±1/2}`. -/
theorem hasPlanarOrder_two_cfEES25 {R : Type u} [Field R] {x : R} (hx1 : x ≠ 1)
    (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    LSSeries.HasPlanarOrder (methodChar (ees25LowStorage x)) 2 := by
  have htab := toRK_ees25LowStorage hx1 hx2 hx3 h2
  refine hasPlanarOrder_two_of_toRK _ ?_ ?_
  · rw [htab]
    have hb := weightBullet_ees25 (x := x) h2
    rw [weightBullet] at hb
    exact hb
  · rw [htab]
    have hc := weight_chain2_ees25 hx1 hx2 hx3 h2
    rw [weight] at hc
    simp only [stageWeight_chain2] at hc
    exact hc

end RungeKutta

end BSeries
