import BSeries.Numerics.Williamson.OrderedMoments
import Mathlib.Algebra.Polynomial.Derivative

/-! # Polynomial realization of the Williamson coefficient path -/

namespace BSeries.WilliamsonMoments

open HopfAlgebras Polynomial
open RungeKutta RungeKutta.LowStorage RungeKutta.WilliamsonPath

noncomputable section

theorem Poly.map_eval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (X : PTree → R) (p : Poly) :
    f (p.eval X) = p.eval (fun t => f (X t)) := by
  induction p with
  | zero => simp [Poly.eval]
  | monomial ts => simp [Poly.eval, map_list_prod, List.map_map, Function.comp_def]
  | add p q hp hq => simp [Poly.eval, hp, hq]
  | scale c p hp => simp [Poly.eval, hp]

theorem Poly.map_rootEval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (V : PTree → R) (p : Poly) :
    f (p.rootEval V) = p.rootEval (fun t => f (V t)) := by
  induction p with
  | zero => simp [Poly.rootEval]
  | monomial ts => rfl
  | add p q hp hq => simp [Poly.rootEval, hp, hq]
  | scale c p hp => simp [Poly.rootEval, hp]

theorem derivative_monomial (X : PTree → ℝ[X]) (ts : List PTree) :
    derivative (ts.map X).prod = dmonomial X (fun t => derivative (X t)) ts := by
  induction ts with
  | nil => simp [dmonomial]
  | cons t ts ih => simp [dmonomial, derivative_mul, ih]

theorem Poly.derivative_eval (X : PTree → ℝ[X]) (p : Poly) :
    derivative (p.eval X) = p.diff X (fun t => derivative (X t)) := by
  induction p with
  | zero => simp [Poly.eval, Poly.diff]
  | monomial ts => exact derivative_monomial X ts
  | add p q hp hq => simp [Poly.eval, Poly.diff, hp, hq]
  | scale c p hp =>
      simp [Poly.eval, Poly.diff, derivative_mul, hp,
        IsScalarTower.algebraMap_eq ℚ ℝ ℝ[X], Polynomial.algebraMap_eq]

variable {s : ℕ}

def momentPrefix (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ :=
  endpoint (extend ls.A) (extend ls.B) (extend (stageWeight ls.toRK t)) e

def momentSlope (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ :=
  extend ls.B e * register (extend ls.A) (extend (stageWeight ls.toRK t)) (e + 1)

def momentPath (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ[X] :=
  C (momentPrefix ls e t) + X * C (momentSlope ls e t)

@[simp] theorem momentPath_derivative (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    derivative (momentPath ls e t) = C (momentSlope ls e t) := by
  simp [momentPath]

@[simp] theorem momentPath_eval_zero (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    (momentPath ls e t).eval 0 = momentPrefix ls e t := by simp [momentPath]

@[simp] theorem momentPath_eval_one (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    (momentPath ls e t).eval 1 = momentPrefix ls (e + 1) t := by
  simp [momentPath, momentPrefix, momentSlope, endpoint]

theorem momentSlope_eq (ls : LowStorage s ℝ) (e : ℕ) (he : e < s) (t : PTree) :
    momentSlope ls e t = ∑ j, ls.beta ⟨e, he⟩ j * stageWeight ls.toRK t j :=
  increment_eq_sum_beta ls _ ⟨e, he⟩

theorem momentPrefix_eq_A (ls : LowStorage s ℝ) (i : Fin s) (t : PTree) :
    momentPrefix ls i t = ∑ j, ls.toRK.A i j * stageWeight ls.toRK t j :=
  endpoint_eq_toRK_A ls _ i

theorem momentPrefix_eq_weight (ls : LowStorage s ℝ) (t : PTree) :
    momentPrefix ls s t = weight ls.toRK t :=
  endpoint_eq_toRK_b ls _

private theorem register_sub (α u v : ℕ → ℝ) (n : ℕ) :
    register α (fun i => u i - v i) n = register α u n - register α v n := by
  induction n with
  | zero => simp [register]
  | succ n ih => simp [register, ih]; ring

theorem momentSlope_area (ls : LowStorage s ℝ) (e : ℕ) (u v : PTree) :
    momentSlope ls e (graft u v) - momentSlope ls e (graft v u) =
      momentPrefix ls e u * momentSlope ls e v -
        momentPrefix ls e v * momentSlope ls e u := by
  have hc : ls.areaColumn (stageWeight ls.toRK u) (stageWeight ls.toRK v) =
      fun i => stageWeight ls.toRK (graft u v) i - stageWeight ls.toRK (graft v u) i := by
    cases u with
    | node us => cases v with
      | node vs => exact areaColumn_stageWeight ls us vs
  have hext := extend_areaColumn ls (stageWeight ls.toRK u) (stageWeight ls.toRK v)
  rw [hc] at hext
  have hext' : extend (fun i => stageWeight ls.toRK (graft u v) i -
      stageWeight ls.toRK (graft v u) i) =
      fun i => extend (stageWeight ls.toRK (graft u v)) i -
        extend (stageWeight ls.toRK (graft v u)) i := by
    funext i; simp [extend]; split <;> simp
  rw [hext'] at hext
  have h := register_bracket (extend ls.A) (extend ls.B)
    (extend (stageWeight ls.toRK u)) (extend (stageWeight ls.toRK v)) e
  rw [← hext, register_sub] at h
  unfold momentSlope momentPrefix
  linear_combination extend ls.B e * h

theorem momentPath_area (ls : LowStorage s ℝ) (e : ℕ) (u v : PTree) :
    derivative (momentPath ls e (graft u v)) - derivative (momentPath ls e (graft v u)) =
      momentPath ls e u * derivative (momentPath ls e v) -
        momentPath ls e v * derivative (momentPath ls e u) := by
  simp only [momentPath_derivative, ← C_sub, momentSlope_area]
  unfold momentPath
  simp only [C_sub, C_mul]
  ring

theorem eval_momentPrefix_node (ls : LowStorage s ℝ) (i : Fin s) (ts : List PTree) :
    (Poly.monomial ts).eval (momentPrefix ls i) = stageWeight ls.toRK (.node ts) i := by
  simp only [Poly.eval, stageWeight_node]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, List.prod_cons, stageWeightList_cons,
        momentPrefix_eq_A, ih]

theorem rootEval_slope (ls : LowStorage s ℝ) (e : ℕ) (he : e < s) (p : Poly) :
    p.rootEval (momentSlope ls e) =
      ∑ i, ls.beta ⟨e, he⟩ i * p.eval (momentPrefix ls i) := by
  induction p with
  | zero => simp [Poly.rootEval, Poly.eval]
  | monomial ts => simp only [Poly.rootEval, momentSlope_eq ls e he, eval_momentPrefix_node]
  | add p q hp hq => simp [Poly.rootEval, Poly.eval, hp, hq, mul_add, Finset.sum_add_distrib]
  | scale c p hp =>
      simp only [Poly.rootEval, Poly.eval, hp, Finset.mul_sum]
      congr 1
      funext i
      ring

/-- The ordered moment polynomial on one straight path segment. -/
def orderedPath (ls : LowStorage s ℝ) (e : ℕ) (ts : List PTree) : ℝ[X] :=
  (orderedForest ts).eval (momentPath ls e)

@[simp] theorem orderedPath_nil (ls : LowStorage s ℝ) (e : ℕ) :
    orderedPath ls e [] = 1 := rfl

/-- Differential recursion of the ordered expansion on a segment. -/
theorem orderedPath_derivative (ls : LowStorage s ℝ) (e : ℕ)
    (ts : List PTree) (t : PTree) :
    derivative (orderedPath ls e (ts ++ [t])) =
      orderedPath ls e ts * C ((orderedTree t).rootEval (momentSlope ls e)) := by
  change derivative ((orderedForest (ts ++ [t])).eval (momentPath ls e)) = _
  rw [orderedForest_append_singleton, Poly.derivative_eval]
  calc
    _ = (orderedForest ts).eval (momentPath ls e) *
        (orderedTree t).rootEval (fun u => derivative (momentPath ls e u)) :=
      Poly.diff_integrate (momentPath ls e) (fun u => derivative (momentPath ls e u))
        (momentPath_area ls e) (orderedForest ts) (orderedTree t)
    _ = _ := by
      simp only [momentPath_derivative]
      apply congrArg ((orderedPath ls e ts) * ·)
      exact (Poly.map_rootEval (Polynomial.CAlgHom : ℝ →ₐ[ℚ] ℝ[X])
        (momentSlope ls e) (orderedTree t)).symm

theorem orderedPath_eval (ls : LowStorage s ℝ) (e : ℕ) (ts : List PTree) (x : ℝ) :
    (orderedPath ls e ts).eval x =
      (orderedForest ts).eval (fun t => (momentPath ls e t).eval x) :=
  by
    simpa only [AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval, orderedPath] using
      Poly.map_eval ((Polynomial.aeval x).restrictScalars ℚ) (momentPath ls e) (orderedForest ts)

end
end BSeries.WilliamsonMoments
