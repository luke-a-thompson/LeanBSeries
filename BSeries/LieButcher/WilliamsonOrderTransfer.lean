import BSeries.LieButcher.CommutatorFreeCharacter
import BSeries.Numerics.Williamson.CommutatorFree
import BSeries.Numerics.Williamson.FlowMoments

/-!
# Williamson order transfer at every order

The order-transfer theorem (`thm:transfer`) of
`papers/williamson_order_transfer.tex`: the Bazavov commutator-free lift of a Williamson 2N scheme inherits the classical
order of the scheme, for every stage count and every order.

The statement uses `CommutatorFreeMethod.HasOrder`, which compares the
Lie–Butcher coefficients of the lift with the exact flow on **all ordered
forests**. The proof has three steps.

1. `LowStorage.toCommutatorFree_methodChar`: the coefficients of the lift,
   defined as the signature of its coefficient path, satisfy the
   chronological recursion `LowStorage.flowChar` (`lem:stages-signature`).
2. `WilliamsonMoments.methodChar_eq_momentPolynomial`: the Williamson area
   identity turns them into universal homogeneous polynomials in the
   classical elementary weights (`lem:area` and `prop:weights`).
3. `WilliamsonMoments.eval_orderedForest_exact`: the same polynomials at
   the exact classical weights give the exact-flow coefficients.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta.LowStorage

variable {R : Type*} [Field R] {s : ℕ}

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

/-- **Lie–Butcher coefficients as signatures** (`lem:stages-signature` of
`papers/williamson_order_transfer.tex`): after
`e` exponentials, the chronological recursion computes the signature of
the first `e` segments of the coefficient path, paired with the stage
vectors of the trees. -/
theorem flowChar_eq_expCoeff (ls : LowStorage s R) (e : ℕ) (he : e ≤ s)
    (ω : PlanarForest) :
    flowChar ls e ω = CommutatorFreeMethod.expCoeff (ls.rows e)
      (ω.map ls.toCommutatorFree.slope) := by
  cases e with
  | zero =>
      rw [flowChar]
      cases ω <;> simp [rows]
  | succ e =>
      rw [flowChar_succ ls e (by omega), rows_succ ls e (by omega),
        CommutatorFreeMethod.expCoeff_concat, List.length_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← List.map_take, ← List.map_drop, List.length_map, List.map_map,
        mul_assoc, flowChar_eq_expCoeff ls e (by omega) (ω.take j)]
      congr 2
      refine congrArg List.prod (List.map_congr_left fun t ht => ?_)
      simp only [Function.comp_apply, StageCombination.eval, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [CommutatorFreeMethod.slope_eq_stageChar, CommutatorFreeMethod.stageChar,
        toCommutatorFree_stageExps_eq_rows,
        flowChar_eq_expCoeff ls i i.isLt.le t.children]
  termination_by (PTree.orderList ω, e)
  decreasing_by
    · rcases lt_or_eq_of_le (PTree.orderList_take_le ω j) with hlt | heq
      · exact Prod.Lex.left _ _ hlt
      · rw [heq]; exact Prod.Lex.right _ (by omega)
    · have h₁ := PTree.order_le_orderList_of_mem ht
      have h₂ := PTree.orderList_drop_le ω j
      have h₃ := PTree.order_eq_one_add_orderList_children t
      exact Prod.Lex.left _ _ (by omega)

/-- The stage coefficients of the Bazavov lift are the flow characters. -/
theorem toCommutatorFree_stageChar (ls : LowStorage s R) (i : Fin s) :
    ls.toCommutatorFree.stageChar i = flowChar ls i := by
  funext ω
  rw [CommutatorFreeMethod.stageChar, toCommutatorFree_stageExps_eq_rows,
    flowChar_eq_expCoeff ls i i.isLt.le]

/-- The Lie–Butcher coefficients of the Bazavov lift, computed from the
general commutator-free expansion, are the method character. -/
theorem toCommutatorFree_methodChar (ls : LowStorage s R) :
    ls.toCommutatorFree.methodChar = ls.methodChar := by
  funext ω
  rw [CommutatorFreeMethod.methodChar, toCommutatorFree_stepExps_eq_rows,
    methodChar, flowChar_eq_expCoeff ls s le_rfl]

end RungeKutta.LowStorage

/-- **Order transfer** (`thm:transfer` of
`papers/williamson_order_transfer.tex`).
If a Williamson 2N Runge–Kutta scheme has classical order `p`, then its
commutator-free lift has order `p` as a Lie-group method: its Lie–Butcher
coefficients match the exact flow on every ordered forest of degree at
most `p`. Any number of stages, any order, and vanishing coefficients or
repeated nodes are allowed. -/
theorem williamson_order_transfer {s p : ℕ} (ls : RungeKutta.LowStorage s ℝ)
    (hRK : RungeKutta.HasOrder ls.toRK p) :
    CommutatorFreeMethod.HasOrder ls.toCommutatorFree p := by
  intro ω hω
  rw [ls.toCommutatorFree_methodChar,
    WilliamsonMoments.methodChar_eq_momentPolynomial]
  calc
    _ = (WilliamsonMoments.orderedForest ω).eval WilliamsonMoments.exactMoment :=
      (WilliamsonMoments.homogeneous_orderedForest ω).eval_congr _ _
        fun t ht => hRK.weight (ht.trans hω)
    _ = OrderedExpansion.exactCoeff ω := WilliamsonMoments.eval_orderedForest_exact ω

/-- info: 'BSeries.williamson_order_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms williamson_order_transfer

/-- **Every Williamson 2N tableau** of classical order `p` is the flat
collapse of a commutator-free method of order `p`. -/
theorem RungeKutta.IsWilliamson2N.exists_commutatorFree_hasOrder {s p : ℕ}
    {rk : RungeKutta (Fin s) ℝ} (h2N : RungeKutta.IsWilliamson2N rk)
    (hRK : RungeKutta.HasOrder rk p) :
    ∃ ls : RungeKutta.LowStorage s ℝ,
      ls.toRK = rk ∧ ls.toCommutatorFree.HasOrder p := by
  obtain ⟨ls, rfl⟩ := h2N
  exact ⟨ls, rfl, williamson_order_transfer ls hRK⟩

/-- Classical order alone does not transfer: Kutta's third-order tableau
has classical order three, but its one-exponential lift, which also
collapses to the tableau on flat spaces, does not have order three. The
Williamson structure is what drives `williamson_order_transfer`. -/
theorem kuttaThirdOrder_not_transfer :
    RungeKutta.HasOrder (RungeKutta.kuttaThirdOrder ℝ) 3 ∧
      ¬ (RungeKutta.kuttaThirdOrder ℝ).toSingleExponential.HasOrder 3 :=
  ⟨RungeKutta.kuttaThirdOrder_hasOrder_three,
    RungeKutta.not_hasOrder_three_toSingleExponential _⟩

end BSeries
