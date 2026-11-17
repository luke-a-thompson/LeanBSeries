import BSeries.LieButcher.ForestOrder
import BSeries.LieButcher.Series

/-!
# Order of a Lie–Butcher character

`LSSeries.exact` is the character of the exact flow on ordered forests
(Owren, *Order conditions for commutator-free Lie group methods*,
Corollary 2.6; equation (10) of the order-transfer manuscript), and
`LSSeries.HasOrder φ p` compares a character with it on every
ordered forest of degree at most `p`. These mirror `Series.exact` and
`Series.HasOrder` on the classical side.

Single trees are not enough from order three: the forests `[•, τ]` and
`[τ, •]` are distinguished by the exact flow.
-/

namespace BSeries

open HopfAlgebras

namespace LSSeries

universe u

variable {R : Type u}

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

/-- **The exact flow as a Lie–Butcher character**: the monomial iterated
integral in equation (10) of the manuscript. A forest `ω` represents the
children of its ordered operator tree, and has degree `PTree.orderList ω`. -/
def exact (R : Type u) [DivisionRing R] : LSSeries R :=
  fun ω => (forestDenominator ω 0 : R)⁻¹

@[simp] theorem exact_nil [DivisionRing R] : exact R [] = 1 := by
  simp [exact, forestDenominator]

/-- The exact-flow recursion, for every ordered forest.
Appending a final tree divides by the total prefix degree. -/
theorem exact_append_singleton [Field R] (ω : PlanarForest) (t : PTree) :
    exact R (ω ++ [t]) =
      exact R ω * exact R t.children /
        ((PTree.orderList ω + PTree.order t : ℕ) : R) := by
  simp only [exact, forestDenominator_append, forestDenominator,
    zero_add, mul_one, treeDenominator_eq, Nat.cast_mul, mul_inv_rev,
    div_eq_mul_inv]
  ring

/-- An LB character has **order** `p` if it matches the exact flow
on every ordered forest of degree at most `p`. -/
def HasOrder [DivisionRing R] (φ : LSSeries R) (p : ℕ) : Prop :=
  ∀ ω : PlanarForest, PTree.orderList ω ≤ p → φ ω = exact R ω

theorem HasOrder.mono [DivisionRing R] {φ : LSSeries R} {p q : ℕ}
    (h : HasOrder φ q) (hpq : p ≤ q) : HasOrder φ p :=
  fun ω hω => h ω (hω.trans hpq)

/-- A normalization check: the two-leaf tree contributes a factor `1/2`
at its stage, then a factor `1/3` at the output. -/
theorem exact_cherry : exact ℚ [PTree.cherry] = 1 / 6 := by
  norm_num [exact, forestDenominator, treeDenominator, PTree.cherry,
    PTree.bullet, PTree.order, PTree.orderList]

end LSSeries

end BSeries
