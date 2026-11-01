import BSeries.LieButcher.CommutatorFreeOrder
import Mathlib.Basic.Real.Basic

/-! # Chronological exact-flow coefficients (equation (10) of the transfer paper) -/

namespace BSeries

open HopfAlgebras

namespace OrderedExpansion

mutual

/-- Denominator associated with the stage coefficient of an ordered tree.
The singleton represents the identity operator in the paper's notation. -/
def treeDenominator : PTree → ℕ
  | .node ts => forestDenominator ts 0

/-- Product of subtree denominators and chronological prefix degrees.
`n` is the degree preceding this suffix of the forest. -/
def forestDenominator : List PTree → ℕ → ℕ
  | [], _ => 1
  | t :: ts, n =>
      (n + PTree.order t) * treeDenominator t *
        forestDenominator ts (n + PTree.order t)

end

theorem treeDenominator_eq (t : PTree) :
    treeDenominator t = forestDenominator t.children 0 := by
  cases t
  rfl

theorem forestDenominator_append (xs ys : List PTree) (n : ℕ) :
    forestDenominator (xs ++ ys) n =
      forestDenominator xs n * forestDenominator ys (n + PTree.orderList xs) := by
  induction xs generalizing n with
  | nil => simp [forestDenominator]
  | cons t ts ih =>
      simp [forestDenominator, ih, PTree.orderList, Nat.add_assoc, Nat.mul_assoc]

/-- Exact chronological coefficient: the monomial iterated integral in
equation (10) of the paper. A forest `ω` represents the children of its
ordered operator tree, and has degree `PTree.orderList ω`. -/
def exactCoeff {R : Type*} [DivisionRing R] (ω : PlanarForest) : R :=
  (forestDenominator ω 0 : R)⁻¹

@[simp] theorem exactCoeff_nil {R : Type*} [DivisionRing R] :
    exactCoeff (R := R) [] = 1 := by
  simp [exactCoeff, forestDenominator]

/-- The exact-flow recursion from equation (10), for every ordered forest.
Appending a final tree divides by the total prefix degree. -/
theorem exactCoeff_append_singleton {R : Type*} [Field R]
    (ω : PlanarForest) (t : PTree) :
    exactCoeff (R := R) (ω ++ [t]) =
      exactCoeff ω * exactCoeff t.children /
        ((PTree.orderList ω + PTree.order t : ℕ) : R) := by
  simp only [exactCoeff, forestDenominator_append, forestDenominator,
    zero_add, mul_one, treeDenominator_eq, Nat.cast_mul, mul_inv_rev,
    div_eq_mul_inv]
  ring

/-- Chronological order includes every ordered forest through degree `p`. -/
def HasOrder {R : Type*} [DivisionRing R] (φ : LSSeries R) (p : ℕ) : Prop :=
  ∀ ω : PlanarForest, PTree.orderList ω ≤ p → φ ω = exactCoeff ω

/-- A normalization check: the two-leaf tree contributes a factor `1/2`
at its stage, then a factor `1/3` at the output. -/
theorem exactCoeff_cherry : exactCoeff (R := ℚ) [PTree.cherry] = 1 / 6 := by
  norm_num [exactCoeff, forestDenominator, treeDenominator, PTree.cherry,
    PTree.bullet, PTree.order, PTree.orderList]

end OrderedExpansion

end BSeries
