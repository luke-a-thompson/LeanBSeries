/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson.Basic
import BSeries.Numerics.CommutatorFree

/-!
# Bazavov's commutator-free lift

A Williamson 2N scheme lifts to a commutator-free method by replacing the
register update `Y_l = Y_{l-1} + B_l δ_l` with the exponential action
`Y_l = Λ(exp(B_l δ_l), Y_{l-1})` (arXiv:2509.20599, equation (4)).
Unrolling the recurrence, the `l`-th exponential argument is
`V_l = Σ_j β_{l,j} K_j`. -/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v w

variable {R : Type v}

namespace LowStorage

variable {s : ℕ} [CommRing R]

/-- Bazavov's commutator-free lift of a Williamson 2N scheme
(arXiv:2509.20599, equation (4)): stage `i` composes the exponentials
`exp(V_m)` for `m < i`, where `V_m = Σ_j β_{m,j} K_j`, and the step
composes all `s` of them. Each stage adds exactly one new exponential, so
the lift uses `s` exponentials per step in two registers. -/
def toCommutatorFree (ls : LowStorage s R) :
    CommutatorFreeMethod (Fin s) R where
  stageExps i := ((List.finRange s).filter (fun m => m < i)).map
    fun m => ls.beta m
  stepExps := (List.finRange s).map fun m => ls.beta m

theorem toCommutatorFree_stageExps (ls : LowStorage s R) (i : Fin s) :
    ls.toCommutatorFree.stageExps i =
      ((List.finRange s).filter (fun m => m < i)).map fun m => ls.beta m :=
  rfl

theorem toCommutatorFree_stepExps (ls : LowStorage s R) :
    ls.toCommutatorFree.stepExps = (List.finRange s).map fun m => ls.beta m :=
  rfl

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

private theorem sum_map_filter_finRange {E : Type w} [AddCommMonoid E]
    (i : Fin s) (f : Fin s → E) :
    ((((List.finRange s).filter (fun m => m < i)).map f).sum) =
      ∑ m ∈ Finset.Iio i, f m := by
  have h1 : ∀ l : List (Fin s), (((l.filter (fun m => m < i)).map f).sum) =
      (l.map fun m => if m < i then f m else 0).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => by_cases h : a < i <;> simp [h, ih]
  rw [h1, ← Fin.sum_univ_def,
    show Finset.Iio i = Finset.univ.filter (fun m => m < i) from by
      ext m; simp,
    Finset.sum_filter]

end LowStorage

namespace LowStorage

variable {s : ℕ} [CommRing R] {E : Type w} [AddCommMonoid E] [Module R E]

/-- **On a flat space the Bazavov lift reproduces the Runge–Kutta stage
values**: composing the lift's stage exponentials under the translation
action yields the stage point of the induced Butcher tableau. -/
theorem toCommutatorFree_stagePoint_translation (ls : LowStorage s R)
    (K : Fin s → E) (i : Fin s) (y : E) :
    ls.toCommutatorFree.stagePoint (ExponentialAction.translation E) K i y =
      y + ∑ j, (toRK ls).A i j • K j := by
  rw [CommutatorFreeMethod.stagePoint,
    ExponentialAction.applyList_translation]
  congr 1
  rw [CommutatorFreeMethod.stageGenerators, toCommutatorFree_stageExps,
    List.map_map, sum_map_filter_finRange]
  simp only [Function.comp_apply, StageCombination.eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toRK_A, Finset.sum_smul]

/-- **On a flat space the Bazavov lift collapses to the classical
Runge–Kutta step** (arXiv:2509.20599, Section 3): the commutator-free
step under the translation action is `y + Σ_j b_j K_j` for the induced
Butcher weights. -/
theorem toCommutatorFree_step_translation (ls : LowStorage s R)
    (K : Fin s → E) (y : E) :
    ls.toCommutatorFree.step (ExponentialAction.translation E) K y =
      y + ∑ j, (toRK ls).b j • K j := by
  rw [CommutatorFreeMethod.step, ExponentialAction.applyList_translation]
  congr 1
  rw [CommutatorFreeMethod.stepGenerators, toCommutatorFree_stepExps,
    List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply, StageCombination.eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toRK_b, Finset.sum_smul]

end LowStorage

end RungeKutta

end BSeries
