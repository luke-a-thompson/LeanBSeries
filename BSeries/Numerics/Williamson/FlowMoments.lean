import BSeries.LieButcher.CommutatorFreeSeries
import BSeries.Numerics.Williamson
import BSeries.Numerics.Williamson.OrderedMoments

/-!
# The exponential lift evaluates the universal moment polynomials

The moment polynomials of a forest, evaluated along the tableau rows, obey
Chen's identity for the coefficient path (`polyFlow_succ`). Induction on the
number of segments identifies them with the signature of that path, and
induction on trees identifies the stage vectors.
-/

namespace BSeries.RungeKutta.LowStorage

variable {R : Type*} [CommRing R] {s : ℕ}

/-- The first `e` segments of the coefficient path: rows of slope weights. -/
def rows (ls : LowStorage s R) (e : ℕ) : List (Fin s → R) :=
  ((List.finRange s).take e).map ls.beta

theorem rows_succ (ls : LowStorage s R) (e : ℕ) (he : e < s) :
    ls.rows (e + 1) = ls.rows e ++ [ls.beta ⟨e, he⟩] := by
  simp [rows, List.take_add_one, he]

private theorem filter_finRange_lt : ∀ {s : ℕ} (i : Fin s),
    (List.finRange s).filter (fun m => m < i) = (List.finRange s).take i
  | 0, i => i.elim0
  | s + 1, i => by
      rw [List.finRange_succ]
      induction i using Fin.cases with
      | zero => simp
      | succ j =>
          simp [List.filter_map, Function.comp_def, filter_finRange_lt j,
            List.map_take]

theorem toCommutatorFree_stageExps_eq_rows (ls : LowStorage s R) (i : Fin s) :
    ls.toCommutatorFree.stageExps i = ls.rows i := by
  rw [toCommutatorFree_stageExps, rows, filter_finRange_lt]

theorem toCommutatorFree_stepExps_eq_rows (ls : LowStorage s R) :
    ls.toCommutatorFree.stepExps = ls.rows s := by
  rw [toCommutatorFree_stepExps, rows, List.take_of_length_le (by simp)]

end BSeries.RungeKutta.LowStorage

namespace BSeries.WilliamsonMoments

open HopfAlgebras RungeKutta RungeKutta.LowStorage
open HopfAlgebras.Word.Polynomial
open scoped BigOperators

noncomputable section

variable {s : ℕ} {K : Type*} [Field K]

def momentPrefix (ls : LowStorage s K) (e : ℕ) (t : PTree) : K :=
  ls.pathPrefix (stageWeight ls.toRK t) e

def momentSlope (ls : LowStorage s K) (e : ℕ) (t : PTree) : K :=
  ls.slope (stageWeight ls.toRK t) e

theorem momentPrefix_succ (ls : LowStorage s K) (e : ℕ) :
    momentPrefix ls (e + 1) = fun t => momentPrefix ls e t + momentSlope ls e t :=
  funext fun _ => prefix_succ ls _ e

theorem momentSlope_eq (ls : LowStorage s K) (e : ℕ) (he : e < s) (t : PTree) :
    momentSlope ls e t = ∑ j, ls.beta ⟨e, he⟩ j * stageWeight ls.toRK t j :=
  slope_coe ls _ ⟨e, he⟩

theorem momentPrefix_eq_A (ls : LowStorage s K) (i : Fin s) (t : PTree) :
    momentPrefix ls i t = ∑ j, ls.toRK.A i j * stageWeight ls.toRK t j :=
  prefix_eq_A ls _ i

theorem momentPrefix_eq_weight (ls : LowStorage s K) (t : PTree) :
    momentPrefix ls s t = weight ls.toRK t :=
  prefix_eq_b ls _

theorem momentSlope_area (ls : LowStorage s K) (e : ℕ) (u v : PTree) :
    momentSlope ls e (graft u v) - momentSlope ls e (graft v u) =
      momentPrefix ls e u * momentSlope ls e v -
        momentPrefix ls e v * momentSlope ls e u := by
  have hc : ls.areaColumn (stageWeight ls.toRK u) (stageWeight ls.toRK v) =
      fun i => stageWeight ls.toRK (graft u v) i - stageWeight ls.toRK (graft v u) i := by
    cases u; cases v; exact areaColumn_stageWeight ls _ _
  have h := slope_area ls (stageWeight ls.toRK u) (stageWeight ls.toRK v) e
  rw [hc] at h
  by_cases he : e < s
  · simpa [momentSlope, momentPrefix, slope, he, mul_sub, Finset.sum_sub_distrib] using h
  · simp [momentSlope, slope, he]

variable [CharZero K]

theorem eval_momentPrefix_node (ls : LowStorage s K) (i : Fin s) (ts : List PTree) :
    (Poly.monomial ts).eval (momentPrefix ls i) = stageWeight ls.toRK (.node ts) i := by
  simp only [Poly.monomial, HopfAlgebras.Word.AreaReduction.Poly.eval_monomial, stageWeight_node]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, List.prod_cons, stageWeightList_cons,
        momentPrefix_eq_A, ih]

theorem rootEval_slope (ls : LowStorage s K) (e : ℕ) (he : e < s) (p : Poly) :
    p.rootEval (momentSlope ls e) =
      ∑ i, ls.beta ⟨e, he⟩ i * p.eval (momentPrefix ls i) := by
  have h : Poly.rootEval (momentSlope ls e) =
      ∑ i, ls.beta ⟨e, he⟩ i • Poly.eval (momentPrefix ls i) := by
    apply linearMap_ext; intro ts
    simpa only [Poly.rootEval, lift_word, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, eval_momentPrefix_node] using momentSlope_eq ls e he (.node ts)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using LinearMap.congr_fun h p

def polyFlow (ls : LowStorage s K) (e : ℕ) (ts : List PTree) : K :=
  (orderedForest ts).eval (momentPrefix ls e)

theorem polyFlow_zero (ls : LowStorage s K) (ts : List PTree) :
    polyFlow ls 0 ts = if ts = [] then 1 else 0 := by
  by_cases h : ts = []
  · subst ts; simp [polyFlow, Poly.eval]
  · rw [ite_eq_right h]
    have hn : 0 < PTree.orderList ts := by
      have := (PTree.orderList_eq_zero_iff ts).not.mpr h
      omega
    change (orderedForest ts).eval (fun t => ls.pathPrefix (stageWeight ls.toRK t) 0) = 0
    simp only [prefix_zero]
    exact (homogeneous_orderedForest ts).eval_zero hn

/-- Moment-polynomial coefficients satisfy the chronological exponential recursion. -/
theorem polyFlow_succ (ls : LowStorage s K) (e : ℕ) (he : e < s) (ts : List PTree) :
    polyFlow ls (e + 1) ts = ∑ j ∈ Finset.range (ts.length + 1),
      polyFlow ls e (ts.take j) * (((ts.drop j).length.factorial : K))⁻¹ *
        (((ts.drop j).map fun t => ∑ i, ls.beta ⟨e, he⟩ i *
          polyFlow ls i t.children).prod) := by
  rw [polyFlow, momentPrefix_succ, eval_orderedForest_add _ _ (momentSlope_area ls e)]
  simp only [rootEval_slope ls e he, orderedTree_eq, polyFlow]

/-- The stage vector of a tree: its moment polynomial at each tableau row. -/
def stageVector (ls : LowStorage s K) (t : PTree) : Fin s → K :=
  fun i => polyFlow ls i t.children

/-- **Lie–Butcher coefficients as signatures** (`lem:stages-signature` of
the order-transfer manuscript): the moment polynomials at the
`e`-th vertex are the signature of the first `e` segments of the
coefficient path, paired with the stage vectors of the trees. -/
theorem polyFlow_eq_expCoeff (ls : LowStorage s K) (e : ℕ) (he : e ≤ s)
    (ts : List PTree) :
    polyFlow ls e ts =
      CommutatorFreeMethod.expCoeff (ls.rows e) (ts.map (stageVector ls)) := by
  induction e generalizing ts with
  | zero =>
      rw [polyFlow_zero]
      cases ts <;> simp [rows]
  | succ e ih =>
      rw [polyFlow_succ ls e (by omega), rows_succ ls e (by omega),
        CommutatorFreeMethod.expCoeff_concat, List.length_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← List.map_take, ← List.map_drop, List.length_map, List.map_map,
        mul_assoc, ih (by omega)]
      rfl

/-- The stage generators of the Bazavov lift are the stage vectors. -/
theorem slope_toCommutatorFree (ls : LowStorage s K) :
    ∀ t : PTree, ls.toCommutatorFree.slope t = stageVector ls t
  | .node ts => by
      funext i
      rw [CommutatorFreeMethod.slope_node, toCommutatorFree_stageExps_eq_rows,
        List.map_congr_left fun t ht => slope_toCommutatorFree ls t,
        ← polyFlow_eq_expCoeff ls i i.isLt.le]
      rfl
  termination_by t => PTree.order t
  decreasing_by exact PTree.order_lt_of_mem_children ht

/-- The Lie–Butcher coefficients of the Bazavov lift are universal
polynomials in the classical elementary weights, at every order and for
every coefficient list. -/
theorem toCommutatorFree_series (ls : LowStorage s K) (ts : List PTree) :
    ls.toCommutatorFree.series ts = (orderedForest ts).eval (weight ls.toRK) := by
  rw [CommutatorFreeMethod.series, toCommutatorFree_stepExps_eq_rows,
    funext (slope_toCommutatorFree ls), ← polyFlow_eq_expCoeff ls s le_rfl, polyFlow,
    funext (momentPrefix_eq_weight ls)]

end
end BSeries.WilliamsonMoments
