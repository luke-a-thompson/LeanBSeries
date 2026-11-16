import HopfAlgebras.Words.AreaReduction
import RoughPaths.Signature.Polynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Area reduction along a straight segment

Let `P w` be moment polynomials indexed by words, with `P (w ++ [b])` a
primitive of `P w` against a letter of constant velocity. Moving the
moments along the straight segment from `X` to `X + V` then multiplies by
a chronological exponential: the deconcatenation formula with factorial
denominators. The area identity for `(X, V)` persists along the segment,
so the hypothesis follows from `diff_primitive`.

Nothing here refers to trees or to a numerical method.
-/

open Polynomial
open HopfAlgebras.Word.Polynomial HopfAlgebras.Word.AreaReduction

namespace BSeries.AreaReduction

noncomputable section

variable {α β : Type*}

theorem Poly.map_eval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (X : α → R) (p : Poly α) :
    f (Poly.eval X p) = Poly.eval (fun a => f (X a)) p := by
  have h : f.toLinearMap.comp (Poly.eval X) = Poly.eval (fun a => f (X a)) := by
    apply linearMap_ext; intro ts
    simp [map_list_prod, List.map_map, Function.comp_def]
  exact LinearMap.congr_fun h p

theorem derivative_monomial (X : α → ℝ[X]) (ts : List α) :
    derivative (ts.map X).prod = dmonomial X (fun a => derivative (X a)) ts := by
  induction ts with
  | nil => simp [dmonomial]
  | cons t ts ih => simp [dmonomial, derivative_mul, ih]

/-- The chain rule for moment polynomials. -/
theorem Poly.derivative_eval (X : α → ℝ[X]) (p : Poly α) :
    derivative (Poly.eval X p) = Poly.diff X (fun a => derivative (X a)) p := by
  have h : (derivative.restrictScalars ℚ).comp (Poly.eval X) =
      Poly.diff X (fun a => derivative (X a)) := by
    apply linearMap_ext; intro ts
    simpa using derivative_monomial X ts
  exact LinearMap.congr_fun h p

/-- The straight segment from `X` to `X + V`, in the segment parameter. -/
def segment (X V : α → ℝ) (a : α) : ℝ[X] :=
  C (X a) + Polynomial.X * C (V a)

@[simp] theorem derivative_segment (X V : α → ℝ) (a : α) :
    derivative (segment X V a) = C (V a) := by simp [segment]

@[simp] theorem segment_eval_zero (X V : α → ℝ) (a : α) :
    (segment X V a).eval 0 = X a := by simp [segment]

@[simp] theorem segment_eval_one (X V : α → ℝ) (a : α) :
    (segment X V a).eval 1 = X a + V a := by simp [segment]

/-- The area identity at the start of a segment holds along all of it. -/
theorem segment_area (graft : α → α → α) (X V : α → ℝ)
    (harea : ∀ u v, V (graft u v) - V (graft v u) = X u * V v - X v * V u) (u v : α) :
    C (V (graft u v)) - C (V (graft v u)) =
      segment X V u * C (V v) - segment X V v * C (V u) := by
  rw [← C_sub, harea]
  simp only [segment, C_sub, C_mul]
  ring

/-- **Chen's identity on a straight segment.** -/
theorem eval_segment (X V : α → ℝ) (P : List β → Poly α) (v : β → ℝ)
    (hnil : P [] = Poly.monomial [])
    (hd : ∀ w b, Poly.diff (segment X V) (fun a => C (V a)) (P (w ++ [b])) =
      Poly.eval (segment X V) (P w) * C (v b)) (w : List β) :
    Poly.eval (fun a => X a + V a) (P w) = ∑ j ∈ Finset.range (w.length + 1),
      Poly.eval X (P (w.take j)) * (((w.drop j).length.factorial : ℝ))⁻¹ *
        ((w.drop j).map v).prod := by
  have h := RoughPaths.Word.PolynomialPath.eval_one
    (fun w => Poly.eval (segment X V) (P w)) v (by simp [hnil])
    (fun w b => by simpa [Poly.derivative_eval] using hd w b) w
  have hev : ∀ (x : ℝ) (p : Poly α), (Poly.eval (segment X V) p).eval x =
      Poly.eval (fun a => (segment X V a).eval x) p := fun x p => by
    simpa only [AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval] using
      Poly.map_eval ((Polynomial.aeval x).restrictScalars ℚ) (segment X V) p
  simpa only [hev, segment_eval_zero, segment_eval_one] using h

end
end BSeries.AreaReduction
