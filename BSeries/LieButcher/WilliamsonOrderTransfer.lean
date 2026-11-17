import BSeries.Numerics.Williamson.FlowMoments

/-!
# Williamson order transfer at every order

The order-transfer theorem (`thm:transfer` of the order-transfer
manuscript): the Bazavov commutator-free lift
of a Williamson 2N scheme inherits the classical order of the scheme, for
every stage count and every order.

The statement uses `CommutatorFreeMethod.HasOrder`, which compares the
Lie–Butcher coefficients of the lift with the exact flow on **all ordered
forests**. The proof has two steps.

1. `WilliamsonMoments.toCommutatorFree_series`: the coefficients of
   the lift, defined as the signature of its coefficient path, are
   universal homogeneous polynomials in the classical elementary weights
   (`lem:stages-signature`, `lem:area` and `prop:weights`).
2. `WilliamsonMoments.eval_orderedForest_exact`: the same polynomials at
   the exact classical weights give the exact-flow coefficients.
-/

namespace BSeries

open HopfAlgebras

/-- **Order transfer** (`thm:transfer` of the order-transfer manuscript).
If a Williamson 2N Runge–Kutta scheme has classical order `p`, then its
commutator-free lift has order `p` as a Lie-group method: its Lie–Butcher
coefficients match the exact flow on every ordered forest of degree at
most `p`. Any number of stages, any order, any field of characteristic
zero, and vanishing coefficients or repeated nodes are allowed. -/
theorem williamson_order_transfer {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    (ls : RungeKutta.LowStorage s K)
    (hRK : RungeKutta.HasOrder ls.toRK p) :
    CommutatorFreeMethod.HasOrder ls.toCommutatorFree p := by
  intro ω hω
  rw [WilliamsonMoments.toCommutatorFree_series]
  calc
    _ = (WilliamsonMoments.orderedForest ω).eval (WilliamsonMoments.exactMoment K) :=
      (WilliamsonMoments.homogeneous_orderedForest ω).eval_congr _ _
        fun t ht => hRK.weight (ht.trans hω)
    _ = LSSeries.exact K ω := WilliamsonMoments.eval_orderedForest_exact K ω

/-- info: 'BSeries.williamson_order_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms williamson_order_transfer

/-- **Every Williamson 2N tableau** of classical order `p` is the flat
collapse of a commutator-free method of order `p`. -/
theorem RungeKutta.IsWilliamson2N.exists_commutatorFree_hasOrder
    {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {rk : RungeKutta (Fin s) K} (h2N : RungeKutta.IsWilliamson2N rk)
    (hRK : RungeKutta.HasOrder rk p) :
    ∃ ls : RungeKutta.LowStorage s K,
      ls.toRK = rk ∧ ls.toCommutatorFree.HasOrder p := by
  obtain ⟨ls, rfl⟩ := h2N
  exact ⟨ls, rfl, williamson_order_transfer ls hRK⟩

/-- On a flat space the single-exponential lift is the Runge–Kutta step. -/
theorem RungeKutta.toSingleExponential_step_translation {ι R : Type*} [Fintype ι] [Semiring R]
    {E : Type*} [AddCommMonoid E] [Module R E] (rk : RungeKutta ι R)
    (K : ι → E) (y : E) :
    rk.toSingleExponential.step (ExponentialAction.translation E) K y =
      y + ∑ j, rk.b j • K j :=
  rfl

/-- Classical order alone does not transfer: Kutta's third-order tableau
has classical order three, but its one-exponential lift, which also
collapses to the tableau on flat spaces, does not have order three. The
Williamson structure is what drives `williamson_order_transfer`. -/
theorem kuttaThirdOrder_not_transfer :
    RungeKutta.HasOrder (RungeKutta.kuttaThirdOrder ℚ) 3 ∧
      ¬ (RungeKutta.kuttaThirdOrder ℚ).toSingleExponential.HasOrder 3 :=
  ⟨RungeKutta.kuttaThirdOrder_hasOrder_three,
    RungeKutta.not_hasOrder_three_toSingleExponential _⟩

end BSeries
