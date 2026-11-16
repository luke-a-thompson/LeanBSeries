import BSeries.LieButcher.CommutatorFreeCharacter
import BSeries.Numerics.Williamson.CommutatorFree
import BSeries.Numerics.Williamson.PolynomialPath
import RoughPaths.Signature.Polynomial

/-!
# The exponential lift evaluates the universal moment polynomials

The moment polynomials of a forest, evaluated along the tableau rows, obey
Chen's identity for the coefficient path (`polyFlow_succ`). Induction on the
number of segments identifies them with the signature of that path, and
induction on trees identifies the stage vectors.
-/

namespace BSeries.WilliamsonMoments

open HopfAlgebras RungeKutta RungeKutta.LowStorage
open scoped BigOperators

noncomputable section

variable {s : ℕ}

def polyFlow (ls : LowStorage s ℝ) (e : ℕ) (ts : List PTree) : ℝ :=
  (orderedForest ts).eval (momentPrefix ls e)

theorem polyFlow_zero (ls : LowStorage s ℝ) (ts : List PTree) :
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
theorem polyFlow_succ (ls : LowStorage s ℝ) (e : ℕ) (he : e < s) (ts : List PTree) :
    polyFlow ls (e + 1) ts = ∑ j ∈ Finset.range (ts.length + 1),
      polyFlow ls e (ts.take j) * (((ts.drop j).length.factorial : ℝ))⁻¹ *
        (((ts.drop j).map fun t => ∑ i, ls.beta ⟨e, he⟩ i *
          polyFlow ls i t.children).prod) := by
  have h := RoughPaths.Word.PolynomialPath.eval_one (orderedPath ls e)
    (fun t => (orderedTree t).rootEval (momentSlope ls e))
    (orderedPath_nil ls e) (orderedPath_derivative ls e) ts
  simp only [orderedPath_eval, momentPath_eval_zero, momentPath_eval_one,
    rootEval_slope ls e he, orderedTree_eq] at h
  exact h

/-- The stage vector of a tree: its moment polynomial at each tableau row. -/
def stageVector (ls : LowStorage s ℝ) (t : PTree) : Fin s → ℝ :=
  fun i => polyFlow ls i t.children

/-- **Lie–Butcher coefficients as signatures** (`lem:stages-signature` of
`papers/williamson_order_transfer.tex`): the moment polynomials at the
`e`-th vertex are the signature of the first `e` segments of the
coefficient path, paired with the stage vectors of the trees. -/
theorem polyFlow_eq_expCoeff (ls : LowStorage s ℝ) (e : ℕ) (he : e ≤ s)
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
theorem slope_toCommutatorFree (ls : LowStorage s ℝ) :
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
theorem toCommutatorFree_methodChar (ls : LowStorage s ℝ) (ts : List PTree) :
    ls.toCommutatorFree.methodChar ts = (orderedForest ts).eval (weight ls.toRK) := by
  rw [CommutatorFreeMethod.methodChar, toCommutatorFree_stepExps_eq_rows,
    funext (slope_toCommutatorFree ls), ← polyFlow_eq_expCoeff ls s le_rfl, polyFlow,
    funext (momentPrefix_eq_weight ls)]

end
end BSeries.WilliamsonMoments
