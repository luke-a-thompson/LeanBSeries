import BSeries.Numerics.CommutatorFree
import BSeries.Numerics.RungeKutta
import BSeries.LieButcher.Order
import RoughPaths.Signature.Piecewise

/-!
# Lie–Butcher series and order of commutator-free methods

A commutator-free method advances by an ordered composition of
exponentials `exp(V₁), …, exp(Vₙ)`, where each `V_m = Σᵢ c_{m,i} Kᵢ`
combines the stage generators `Kᵢ = F(Yᵢ)`, and each stage point `Yᵢ` is
itself such a composition applied to the initial point (Owren, *Order
conditions for commutator-free Lie group methods*, Section 2).

Expanding in ordered products of frozen elementary differentials gives
coefficients indexed by planar forests. A composition of exponentials is
the **signature of the piecewise-linear coefficient path** with one
straight segment per exponential:

* `expCoeff cs` is that signature, paired with a word of stage vectors;
* `slope τ i` is the coefficient of the elementary differential `F(τ)`
  in `Kᵢ`, obtained by substituting the stage expansion into `F`;
* `stageSeries i` and `series` are the coefficients of the stage point
  `Yᵢ` and of the step.

`HasOrder cf p` compares `series` with the exact flow on **every
ordered forest** of degree at most `p`. It never mentions a Butcher
tableau, and is not implied by classical order: a method whose step is a
single exponential never has order three
(`not_hasOrder_three_of_stepExps_singleton`), although its flat collapse
can be a classical Runge–Kutta method of any order.
-/

namespace BSeries

open HopfAlgebras RoughPaths

open scoped BigOperators

namespace CommutatorFreeMethod

universe u v

variable {ι : Type u} {R : Type v} [Fintype ι] [Field R]

/-- Coefficients of an ordered composition of exponentials, on a word of
stage vectors: the signature of the piecewise-linear path whose `m`-th
segment has increment `k ↦ Σᵢ c_{m,i} kᵢ`. The head of the list is the
exponential applied first, as in `ExponentialAction.applyList`. -/
def expCoeff (cs : List (StageCombination ι R)) : List (ι → R) → R :=
  Word.piecewiseLinearSignature (cs.map fun c k => StageCombination.eval c k)

@[simp]
theorem expCoeff_nil_nil : expCoeff ([] : List (StageCombination ι R)) [] = 1 :=
  rfl

@[simp]
theorem expCoeff_nil_cons (k : ι → R) (w : List (ι → R)) :
    expCoeff ([] : List (StageCombination ι R)) (k :: w) = 0 :=
  rfl

/-- One exponential is symmetric in its arguments, with factorial weight. -/
theorem expCoeff_singleton (c : StageCombination ι R) (w : List (ι → R)) :
    expCoeff [c] w =
      (w.map fun k => StageCombination.eval c k).prod / (w.length.factorial : R) := by
  simp [expCoeff, Word.linearSignature]

private theorem splits_eq_map_range {α : Type*} :
    ∀ w : List α, Word.splits w =
      (List.range (w.length + 1)).map fun j => (w.take j, w.drop j)
  | [] => rfl
  | x :: w => by
      rw [Word.splits_cons, splits_eq_map_range w, List.length_cons,
        List.range_succ_eq_map (n := w.length + 1)]
      simp [Function.comp_def]

/-- Chen's identity for appending one exponential: the ordered factors of
a forest are split between the earlier exponentials and the last one. -/
theorem expCoeff_concat (cs : List (StageCombination ι R))
    (c : StageCombination ι R) (w : List (ι → R)) :
    expCoeff (cs ++ [c]) w = ∑ j ∈ Finset.range (w.length + 1),
      expCoeff cs (w.take j) * (((w.drop j).length.factorial : R)⁻¹ *
        ((w.drop j).map fun k => StageCombination.eval c k).prod) := by
  rw [expCoeff, List.map_append, Word.piecewiseLinearSignature_append,
    List.map_singleton, Word.piecewiseLinearSignature_singleton,
    Word.tensorProduct, splits_eq_map_range, List.map_map,
    list_range_map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, Word.coeff, Word.linearSignature, expCoeff,
    div_eq_inv_mul]

/-- The coefficient of the elementary differential `F(τ)` in the stage
generator `Kᵢ = F(Yᵢ)`: the expansion of the stage point `Yᵢ`, evaluated
on the branches of `τ`. -/
def slope (cf : CommutatorFreeMethod ι R) : PTree → ι → R
  | .node ts => fun i =>
      expCoeff (cf.stageExps i) (ts.attach.map fun τ => slope cf τ.1)
  termination_by τ => PTree.order τ
  decreasing_by exact PTree.order_lt_of_mem_children τ.2

theorem slope_node (cf : CommutatorFreeMethod ι R) (ts : List PTree) (i : ι) :
    cf.slope (.node ts) i = expCoeff (cf.stageExps i) (ts.map cf.slope) := by
  rw [slope, List.attach_map_val (f := cf.slope)]

/-- Lie–Butcher coefficients of the `i`-th stage point. -/
def stageSeries (cf : CommutatorFreeMethod ι R) (i : ι) : LSSeries R :=
  fun ω => expCoeff (cf.stageExps i) (ω.map cf.slope)

/-- Lie–Butcher coefficients of one step of the method. -/
def series (cf : CommutatorFreeMethod ι R) : LSSeries R :=
  fun ω => expCoeff cf.stepExps (ω.map cf.slope)

/-- Stage generators are the vector field evaluated at the stage points. -/
theorem slope_eq_stageSeries (cf : CommutatorFreeMethod ι R) (τ : PTree) (i : ι) :
    cf.slope τ i = cf.stageSeries i τ.children := by
  cases τ
  exact cf.slope_node _ i

/-- A commutator-free method has **order `p`** if its Lie–Butcher
coefficients agree with those of the exact flow on every ordered forest
of degree at most `p`. -/
def HasOrder (cf : CommutatorFreeMethod ι R) (p : ℕ) : Prop :=
  LSSeries.HasOrder cf.series p

theorem HasOrder.mono {cf : CommutatorFreeMethod ι R} {p q : ℕ}
    (h : cf.HasOrder q) (hpq : p ≤ q) : cf.HasOrder p :=
  LSSeries.HasOrder.mono h hpq

/-! ### Checks of the definition -/

/-- The step of a commutator-free method is a Lie-group integrator: its
coefficients form a shuffle character. -/
theorem isExponential_series [CharZero R] (cf : CommutatorFreeMethod ι R) :
    LSSeries.IsExponential cf.series := by
  have h := (Word.isGroupLike_piecewiseLinearSignature
    (cf.stepExps.map fun c k => StageCombination.eval c k)).comapMapLetters cf.slope
  exact ⟨h.1, fun ω₁ ω₂ => (h.2 ω₁ ω₂).symm⟩

/-- The method with no exponentials is the identity map. -/
theorem identity_series (ω : PlanarForest) :
    (identity ι R).series ω = if ω = [] then 1 else 0 := by
  cases ω <;> simp [series, identity]

/-- A single-exponential step treats the trees of a forest symmetrically. -/
theorem series_perm_of_stepExps_singleton (cf : CommutatorFreeMethod ι R)
    {c : StageCombination ι R} (hc : cf.stepExps = [c]) {ω ω' : PlanarForest}
    (h : ω.Perm ω') : cf.series ω = cf.series ω' := by
  simp only [series, hc, expCoeff_singleton, List.map_map, List.length_map]
  rw [(h.map _).prod_eq, h.length_eq]

/-- **Order barrier**: one exponential per step cannot reach order three,
because the exact flow distinguishes the two orderings of a leaf and a
two-chain. Lie-group order is therefore strictly more than classical
order of the flat collapse. -/
theorem not_hasOrder_three_of_stepExps_singleton [CharZero R]
    (cf : CommutatorFreeMethod ι R) {c : StageCombination ι R}
    (hc : cf.stepExps = [c]) : ¬ cf.HasOrder 3 := by
  intro h
  have h1 := h [PTree.bullet, PTree.chain2] (by decide)
  have h2 := h [PTree.chain2, PTree.bullet] (by decide)
  rw [cf.series_perm_of_stepExps_singleton hc (List.Perm.swap _ _ _), h2] at h1
  norm_num [LSSeries.exact, LSSeries.forestDenominator,
    LSSeries.treeDenominator, PTree.bullet, PTree.chain2, PTree.order,
    PTree.orderList] at h1

/-- The Lie–Euler method `y ↦ exp(F(y)) y` expands as the frozen
exponential `LSSeries.exactFlow`: `1/n!` on `n` leaves, and zero on every
other forest. -/
theorem singleExponential_series [DecidableEq PlanarTree] :
    (singleExponential.{v, u} R).series = LSSeries.exactFlow R := by
  funext ω
  have hslope : ∀ t : PTree, (singleExponential.{v, u} R).slope t PUnit.unit =
      if t = PTree.bullet then 1 else 0 := by
    rintro ⟨_ | ⟨t, ts⟩⟩ <;> simp [slope_node, singleExponential, PTree.bullet]
  simp only [series, show (singleExponential.{v, u} R).stepExps = [fun _ => 1] from rfl,
    expCoeff_singleton, List.map_map, List.length_map, Function.comp_def,
    StageCombination.eval_punit, smul_eq_mul, one_mul, div_eq_inv_mul,
    LSSeries.exactFlow, funext hslope]
  split_ifs with hω
  · rw [List.map_congr_left fun t ht => ite_eq_left (hω t ht)]
    simp
  · push Not at hω
    obtain ⟨t, ht, hne⟩ := hω
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨t, ht, ite_eq_right hne⟩), mul_zero]

/-- Lie–Euler has order one. -/
theorem singleExponential_hasOrder_one : (singleExponential.{v, u} R).HasOrder 1 := by
  classical
  intro ω hω
  rw [singleExponential_series, LSSeries.exactFlow]
  match ω, hω with
  | [], _ => simp
  | [t], h =>
      have ht : t = PTree.bullet := (PTree.order_eq_one_iff t).mp
        (le_antisymm (by simpa [PTree.orderList] using h) (PTree.order_pos t))
      subst ht
      simp [LSSeries.exact, LSSeries.forestDenominator,
        LSSeries.treeDenominator, PTree.bullet, PTree.orderList]
  | t :: u :: ω, h =>
      have := PTree.order_pos t
      have := PTree.order_pos u
      simp only [PTree.orderList_cons] at h
      omega

/-- Lie–Euler does not have order two. -/
theorem singleExponential_not_hasOrder_two [CharZero R] :
    ¬ (singleExponential.{v, u} R).HasOrder 2 := by
  classical
  intro h
  have h1 := h [PTree.chain2] (by decide)
  rw [singleExponential_series, LSSeries.exactFlow,
    ite_eq_right (by simp [PTree.chain2, PTree.bullet])] at h1
  norm_num [LSSeries.exact, LSSeries.forestDenominator,
    LSSeries.treeDenominator, PTree.bullet, PTree.chain2, PTree.order,
    PTree.orderList] at h1

end CommutatorFreeMethod

/-! ### Classical order does not transfer through a single exponential -/

namespace RungeKutta

universe u v

variable {ι : Type u} {R : Type v}

/-- The lift of a tableau with one exponential per stage and per step:
`Yᵢ = exp(Σⱼ aᵢⱼ Kⱼ) y` and `y₁ = exp(Σⱼ bⱼ Kⱼ) y`. -/
def toSingleExponential (rk : RungeKutta ι R) : CommutatorFreeMethod ι R where
  stageExps i := [rk.A i]
  stepExps := [rk.b]

/-- Whatever the classical order of the tableau, its single-exponential
lift does not have order three. -/
theorem not_hasOrder_three_toSingleExponential [Fintype ι] [Field R] [CharZero R]
    (rk : RungeKutta ι R) : ¬ rk.toSingleExponential.HasOrder 3 :=
  CommutatorFreeMethod.not_hasOrder_three_of_stepExps_singleton _ rfl

end RungeKutta

end BSeries
