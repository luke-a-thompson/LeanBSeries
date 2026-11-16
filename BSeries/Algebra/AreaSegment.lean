import HopfAlgebras.Words.AreaReduction
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.FieldSimp

/-!
# Area reduction along a straight segment

Let `P w` be moment polynomials indexed by words, with `P (w ++ [b])` a
primitive of `P w` against a letter of constant velocity. Moving the
moments along the straight segment from `X` to `X + V` then multiplies by
a chronological exponential: the deconcatenation formula with factorial
denominators. The area identity for `(X, V)` persists along the segment,
so the hypothesis follows from `diff_primitive`.

Nothing here refers to trees or to a numerical method, and the scalars are
any field of characteristic zero.
-/

open Polynomial
open HopfAlgebras.Word.Polynomial HopfAlgebras.Word.AreaReduction

namespace BSeries.AreaReduction

noncomputable section

variable {α β K : Type*} [Field K] [CharZero K]

/-! ### Polynomial solutions of the chronological word recursion -/

section Chronological

variable (P : List β → K[X]) (v : β → K)
    (hnil : P [] = 1)
    (hd : ∀ w b, derivative (P (w ++ [b])) = P w * C (v b))

include hnil hd

theorem chronological_coeff (w : List β) (n : ℕ) :
    (P w).coeff n = if n ≤ w.length then
      (P (w.take (w.length - n))).eval 0 * (n.factorial : K)⁻¹ *
        ((w.drop (w.length - n)).map v).prod else 0 := by
  induction n generalizing w with
  | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ n ih =>
      cases w using List.reverseRecOn with
      | nil => simp [hnil, Polynomial.coeff_one]
      | append_singleton w t =>
          have hn : (n + 1 : K) ≠ 0 := Nat.cast_add_one_ne_zero n
          have hc := congrArg (fun q : K[X] => q.coeff n) (hd w t)
          rw [coeff_derivative, coeff_mul_C, ih] at hc
          by_cases h : n ≤ w.length
          · rw [ite_eq_left h] at hc
            have hc' := (eq_div_iff hn).mpr hc
            rw [hc']
            simp only [List.length_append, List.length_singleton, Nat.add_sub_add_right]
            rw [ite_eq_left (by omega), List.take_append_of_le_length (Nat.sub_le _ _),
              List.drop_append_of_le_length (Nat.sub_le _ _)]
            simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
              List.prod_cons, List.prod_nil, mul_one, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one, mul_inv_rev]
            field_simp
          · rw [ite_eq_right h, zero_mul] at hc
            have hz := (mul_eq_zero.mp hc).resolve_right hn
            rw [hz, ite_eq_right (by simp; omega)]

/-- A word recursion with constant velocities is a chronological
exponential: the deconcatenation formula with factorial denominators. -/
theorem chronological_eval_one (w : List β) :
    (P w).eval 1 = ∑ j ∈ Finset.range (w.length + 1),
      (P (w.take j)).eval 0 * (((w.drop j).length.factorial : K))⁻¹ *
        ((w.drop j).map v).prod := by
  have hdeg : (P w).natDegree ≤ w.length :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
      rw [chronological_coeff P v hnil hd, ite_eq_right (by omega)]
  rw [Polynomial.eval_eq_sum_range' (n := w.length + 1) (by omega)]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [chronological_coeff P v hnil hd]
  simp only [Nat.add_sub_cancel, List.length_drop]
  rw [ite_eq_left (by omega), Nat.sub_sub_self (by omega)]

end Chronological

/-! ### Moment polynomials along a segment -/

theorem Poly.map_eval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (X : α → R) (p : Poly α) :
    f (Poly.eval X p) = Poly.eval (fun a => f (X a)) p := by
  have h : f.toLinearMap.comp (Poly.eval X) = Poly.eval (fun a => f (X a)) := by
    apply linearMap_ext; intro ts
    simp [map_list_prod, List.map_map, Function.comp_def]
  exact LinearMap.congr_fun h p

theorem derivative_monomial (X : α → K[X]) (ts : List α) :
    derivative (ts.map X).prod = dmonomial X (fun a => derivative (X a)) ts := by
  induction ts with
  | nil => simp [dmonomial]
  | cons t ts ih => simp [dmonomial, derivative_mul, ih]

/-- The chain rule for moment polynomials. -/
theorem Poly.derivative_eval (X : α → K[X]) (p : Poly α) :
    derivative (Poly.eval X p) = Poly.diff X (fun a => derivative (X a)) p := by
  have h : (derivative.restrictScalars ℚ).comp (Poly.eval X) =
      Poly.diff X (fun a => derivative (X a)) := by
    apply linearMap_ext; intro ts
    simpa using derivative_monomial X ts
  exact LinearMap.congr_fun h p

/-- The straight segment from `X` to `X + V`, in the segment parameter. -/
def segment (X V : α → K) (a : α) : K[X] :=
  C (X a) + Polynomial.X * C (V a)

@[simp] theorem derivative_segment (X V : α → K) (a : α) :
    derivative (segment X V a) = C (V a) := by simp [segment]

@[simp] theorem segment_eval_zero (X V : α → K) (a : α) :
    (segment X V a).eval 0 = X a := by simp [segment]

@[simp] theorem segment_eval_one (X V : α → K) (a : α) :
    (segment X V a).eval 1 = X a + V a := by simp [segment]

/-- The area identity at the start of a segment holds along all of it. -/
theorem segment_area (graft : α → α → α) (X V : α → K)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u) (u v : α) :
    C (V (graft u v)) - C (V (graft v u)) =
      segment X V u * C (V v) - segment X V v * C (V u) := by
  rw [← C_sub, harea]
  simp only [segment, C_sub, C_mul]
  ring

/-- **Chen's identity on a straight segment.** -/
theorem eval_segment (X V : α → K) (P : List β → Poly α) (v : β → K)
    (hnil : P [] = Poly.monomial [])
    (hd : ∀ w b, Poly.diff (segment X V) (fun a => C (V a)) (P (w ++ [b])) =
      Poly.eval (segment X V) (P w) * C (v b)) (w : List β) :
    Poly.eval (fun a => X a + V a) (P w) = ∑ j ∈ Finset.range (w.length + 1),
      Poly.eval X (P (w.take j)) * (((w.drop j).length.factorial : K))⁻¹ *
        ((w.drop j).map v).prod := by
  have h := chronological_eval_one
    (fun w => Poly.eval (segment X V) (P w)) v (by simp [hnil])
    (fun w b => by simpa [Poly.derivative_eval] using hd w b) w
  have hev : ∀ (x : K) (p : Poly α), (Poly.eval (segment X V) p).eval x =
      Poly.eval (fun a => (segment X V a).eval x) p := fun x p => by
    simpa only [AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval] using
      Poly.map_eval ((Polynomial.aeval x).restrictScalars ℚ) (segment X V) p
  simpa only [hev, segment_eval_zero, segment_eval_one] using h

end
end BSeries.AreaReduction
