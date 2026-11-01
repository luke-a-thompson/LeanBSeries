import BSeries.Numerics.Williamson.FlowMoments

/-!
# Williamson order transfer at every order

Theorem 5 of `papers/williamson_order_transfer.tex` compares **all ordered
forests**, using the chronological exact-flow recursion (equation (10)).
These coefficients differ from ordinary unordered-tree factorials.

The area identity constructs universal homogeneous moment polynomials.
`WilliamsonMoments.methodChar_eq_momentPolynomial` identifies their evaluation
with the actual exponential lift. `WilliamsonMoments.eval_orderedForest_exact`
identifies their exact-flow specialization. Substituting the classical
order conditions proves the result, for every stage count and order.
-/

namespace BSeries

/-- **Order transfer**, Theorem 5 of `williamson_order_transfer.pdf`.
Classical order `p` of any finite Williamson list implies chronological
order `p` of its exponential lift. Zero coefficients and repeated nodes
are permitted. The conclusion uses all ordered forests through degree `p`. -/
theorem WilliamsonOrderTransfer (s : ℕ) (ls : RungeKutta.LowStorage s ℝ) (p : ℕ)
    (h : RungeKutta.HasOrder ls.toRK p) :
    OrderedExpansion.HasOrder ls.methodChar p := by
  intro ts hts
  rw [WilliamsonMoments.methodChar_eq_momentPolynomial]
  calc
    _ = (WilliamsonMoments.orderedForest ts).eval WilliamsonMoments.exactMoment :=
      (WilliamsonMoments.homogeneous_orderedForest ts).eval_congr _ _
        (fun t ht => h.weight (ht.trans hts))
    _ = OrderedExpansion.exactCoeff ts := WilliamsonMoments.eval_orderedForest_exact ts

end BSeries
