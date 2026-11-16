import BSeries.LieButcher.CommutatorFreeOrder
import BSeries.Numerics.Williamson.PolynomialPath
import RoughPaths.Signature.Polynomial

/-! # The exponential lift evaluates the universal moment polynomials -/

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

/-- The universal polynomial gives every numerical prefix coefficient.
The induction follows the existing `flowChar` recursion and has no order bound. -/
theorem flowChar_eq_polyFlow (ls : LowStorage s ℝ) (e : ℕ)
    (ts : List PTree) (he : e ≤ s) : flowChar ls e ts = polyFlow ls e ts := by
  cases e with
  | zero => rw [flowChar, polyFlow_zero]
  | succ e =>
      rw [flowChar_succ ls e (by omega), polyFlow_succ ls e (by omega)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [flowChar_eq_polyFlow ls e (ts.take j) (by omega)]
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro t ht
      apply Finset.sum_congr rfl
      intro i _
      rw [flowChar_eq_polyFlow ls i t.children i.isLt.le]
  termination_by (PTree.orderList ts, e)
  decreasing_by
    · have hle := PTree.orderList_take_le ts j
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Prod.Lex.left _ _ hlt
      · rw [heq]; exact Prod.Lex.right _ (by omega)
    · have h₁ := PTree.order_le_orderList_of_mem ht
      have h₂ := PTree.orderList_drop_le ts j
      have h₃ := PTree.order_eq_one_add_orderList_children t
      exact Prod.Lex.left _ _ (by omega)

/-- Lemma 3 and the ordered-tree induction, as an identity for the actual
`LowStorage.methodChar`, at every order and for every coefficient list. -/
theorem methodChar_eq_momentPolynomial (ls : LowStorage s ℝ) (ts : List PTree) :
    ls.methodChar ts = (orderedForest ts).eval (weight ls.toRK) := by
  rw [methodChar, flowChar_eq_polyFlow ls s ts le_rfl]
  have h : momentPrefix ls s = weight ls.toRK := funext (momentPrefix_eq_weight ls)
  simp only [polyFlow, h]

end
end BSeries.WilliamsonMoments
