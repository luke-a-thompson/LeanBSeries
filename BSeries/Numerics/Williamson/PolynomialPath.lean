import BSeries.Numerics.Williamson.OrderedMoments
import Mathlib.Algebra.Polynomial.Derivative

/-! # Polynomial realization of the Williamson coefficient path -/

namespace BSeries.WilliamsonMoments

open HopfAlgebras Polynomial
open HopfAlgebras.Word.Polynomial
open RungeKutta RungeKutta.LowStorage

noncomputable section

theorem Poly.map_eval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (X : PTree → R) (p : Poly) :
    f (p.eval X) = p.eval (fun t => f (X t)) := by
  have h : f.toLinearMap.comp (eval X) = eval (fun t => f (X t)) := by
    apply linearMap_ext; intro ts
    simp [eval, map_list_prod, List.map_map, Function.comp_def]
  exact LinearMap.congr_fun h p

theorem Poly.map_rootEval {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (V : PTree → R) (p : Poly) :
    f (p.rootEval V) = p.rootEval (fun t => f (V t)) := by
  have h : f.toLinearMap.comp (rootEval V) = rootEval (fun t => f (V t)) := by
    apply linearMap_ext; intro ts
    simp [rootEval]
  exact LinearMap.congr_fun h p

theorem derivative_monomial (X : PTree → ℝ[X]) (ts : List PTree) :
    derivative (ts.map X).prod = dmonomial X (fun t => derivative (X t)) ts := by
  induction ts with
  | nil => simp [dmonomial]
  | cons t ts ih => simp [dmonomial, derivative_mul, ih]

theorem Poly.derivative_eval (X : PTree → ℝ[X]) (p : Poly) :
    derivative (p.eval X) = p.diff X (fun t => derivative (X t)) := by
  have h : (derivative.restrictScalars ℚ).comp (eval X) =
      diff X (fun t => derivative (X t)) := by
    apply linearMap_ext; intro ts
    simpa [eval, diff, HopfAlgebras.Word.AreaReduction.Poly.diff] using derivative_monomial X ts
  exact LinearMap.congr_fun h p

variable {s : ℕ}

def momentPrefix (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ :=
  ls.pathPrefix (stageWeight ls.toRK t) e

def momentSlope (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ :=
  ls.slope (stageWeight ls.toRK t) e

def momentPath (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) : ℝ[X] :=
  C (momentPrefix ls e t) + X * C (momentSlope ls e t)

@[simp] theorem momentPath_derivative (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    derivative (momentPath ls e t) = C (momentSlope ls e t) := by
  simp [momentPath]

@[simp] theorem momentPath_eval_zero (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    (momentPath ls e t).eval 0 = momentPrefix ls e t := by simp [momentPath]

@[simp] theorem momentPath_eval_one (ls : LowStorage s ℝ) (e : ℕ) (t : PTree) :
    (momentPath ls e t).eval 1 = momentPrefix ls (e + 1) t := by
  simp [momentPath, momentPrefix, momentSlope, prefix_succ]

theorem momentSlope_eq (ls : LowStorage s ℝ) (e : ℕ) (he : e < s) (t : PTree) :
    momentSlope ls e t = ∑ j, ls.beta ⟨e, he⟩ j * stageWeight ls.toRK t j :=
  slope_coe ls _ ⟨e, he⟩

theorem momentPrefix_eq_A (ls : LowStorage s ℝ) (i : Fin s) (t : PTree) :
    momentPrefix ls i t = ∑ j, ls.toRK.A i j * stageWeight ls.toRK t j :=
  prefix_eq_A ls _ i

theorem momentPrefix_eq_weight (ls : LowStorage s ℝ) (t : PTree) :
    momentPrefix ls s t = weight ls.toRK t :=
  prefix_eq_b ls _

theorem momentSlope_area (ls : LowStorage s ℝ) (e : ℕ) (u v : PTree) :
    momentSlope ls e (graft u v) - momentSlope ls e (graft v u) =
      momentPrefix ls e u * momentSlope ls e v -
        momentPrefix ls e v * momentSlope ls e u := by
  have hc : ls.areaColumn (stageWeight ls.toRK u) (stageWeight ls.toRK v) =
      fun i => stageWeight ls.toRK (graft u v) i - stageWeight ls.toRK (graft v u) i := by
    cases u; cases v; exact areaColumn_stageWeight ls _ _
  have h := slope_area ls (stageWeight ls.toRK u) (stageWeight ls.toRK v) e
  rw [hc] at h
  by_cases he : e < s
  · simpa [momentSlope, momentPrefix, slope, he, mul_sub, Finset.sum_sub_distrib] using h
  · simp [momentSlope, slope, he]

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
  simp only [Poly.monomial, HopfAlgebras.Word.AreaReduction.Poly.eval_monomial, stageWeight_node]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, List.prod_cons, stageWeightList_cons,
        momentPrefix_eq_A, ih]

theorem rootEval_slope (ls : LowStorage s ℝ) (e : ℕ) (he : e < s) (p : Poly) :
    p.rootEval (momentSlope ls e) =
      ∑ i, ls.beta ⟨e, he⟩ i * p.eval (momentPrefix ls i) := by
  have h : Poly.rootEval (momentSlope ls e) =
      ∑ i, ls.beta ⟨e, he⟩ i • Poly.eval (momentPrefix ls i) := by
    apply linearMap_ext; intro ts
    simpa only [Poly.rootEval, lift_word, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, eval_momentPrefix_node] using momentSlope_eq ls e he (.node ts)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using LinearMap.congr_fun h p

/-- The ordered moment polynomial on one straight path segment. -/
def orderedPath (ls : LowStorage s ℝ) (e : ℕ) (ts : List PTree) : ℝ[X] :=
  (orderedForest ts).eval (momentPath ls e)

@[simp] theorem orderedPath_nil (ls : LowStorage s ℝ) (e : ℕ) :
    orderedPath ls e [] = 1 := by
  simp [orderedPath, Poly.eval, Poly.monomial]

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
