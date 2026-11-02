import BSeries.Numerics.Williamson.Basic
import Mathlib.Tactic.Ring

/-! # Area closure of the finite Williamson coefficient path

The path uses the rows of `beta` directly. Its prefixes are the rows of
`toRK.A`, and its endpoint is `toRK.b`. No coefficient is divided out.
-/

namespace BSeries.RungeKutta.LowStorage

open scoped BigOperators
variable {R : Type*} [CommRing R] {s : ℕ}

/-- A scalar projection of the coefficient path at a stage boundary. -/
def pathPrefix (ls : LowStorage s R) (u : Fin s → R) (n : ℕ) : R :=
  ∑ i, if i.val < n then ∑ j, ls.beta i j * u j else 0

/-- A scalar projection of one segment increment. -/
def slope (ls : LowStorage s R) (u : Fin s → R) (n : ℕ) : R :=
  if h : n < s then ∑ j, ls.beta ⟨n, h⟩ j * u j else 0

@[simp] theorem prefix_zero (ls : LowStorage s R) (u : Fin s → R) :
    ls.pathPrefix u 0 = 0 := by simp [pathPrefix]

@[simp] theorem slope_coe (ls : LowStorage s R) (u : Fin s → R) (i : Fin s) :
    ls.slope u i = ∑ j, ls.beta i j * u j := by simp [slope, i.isLt]

theorem prefix_succ (ls : LowStorage s R) (u : Fin s → R) (n : ℕ) :
    ls.pathPrefix u (n + 1) = ls.pathPrefix u n + ls.slope u n := by
  classical
  by_cases hn : n < s
  · have hsplit : ∀ i : Fin s,
        (if i.val < n + 1 then ∑ j, ls.beta i j * u j else 0) =
        (if i.val < n then ∑ j, ls.beta i j * u j else 0) +
          (if i = ⟨n, hn⟩ then ∑ j, ls.beta i j * u j else 0) := by
      intro i
      simp only [Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    simp only [pathPrefix, hsplit, Finset.sum_add_distrib, slope, dite_eq_left hn]
    simp
  · have hi (i : Fin s) : i.val < n := lt_of_lt_of_le i.isLt (by omega)
    simp [pathPrefix, slope, hn, hi, fun i => Nat.lt_succ_of_lt (hi i)]

theorem prefix_eq_A (ls : LowStorage s R) (u : Fin s → R) (i : Fin s) :
    ls.pathPrefix u i = ∑ j, ls.toRK.A i j * u j := by
  simp_rw [pathPrefix, toRK_A, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]

theorem prefix_eq_b (ls : LowStorage s R) (u : Fin s → R) :
    ls.pathPrefix u s = ∑ j, ls.toRK.b j * u j := by
  simp only [pathPrefix, Fin.isLt, ite_true, toRK_b, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Coefficients of the increment register, before scaling by `B`. -/
def registerCoeff (ls : LowStorage s R) (i j : Fin s) : R :=
  if j ≤ i then ls.prodA j i else 0

theorem beta_eq_mul_registerCoeff (ls : LowStorage s R) (i j : Fin s) :
    ls.beta i j = ls.B i * ls.registerCoeff i j := by
  unfold beta registerCoeff
  split_ifs <;> simp

private theorem registerCoeff_zero (ls : LowStorage s R) (hs : 0 < s)
    (j : Fin s) :
    ls.registerCoeff ⟨0, hs⟩ j = if j = ⟨0, hs⟩ then 1 else 0 := by
  by_cases hj : j = ⟨0, hs⟩
  · subst j; simp [registerCoeff]
  · have : ¬ j ≤ (⟨0, hs⟩ : Fin s) := fun h => hj (Fin.ext (Nat.eq_zero_of_le_zero h))
    simp [registerCoeff, hj, this]

private theorem registerCoeff_succ (ls : LowStorage s R) (n : ℕ)
    (hn : n + 1 < s) (j : Fin s) :
    ls.registerCoeff ⟨n + 1, hn⟩ j =
      ls.A ⟨n + 1, hn⟩ * ls.registerCoeff ⟨n, by omega⟩ j +
        if j = ⟨n + 1, hn⟩ then 1 else 0 := by
  rcases lt_trichotomy j.val (n + 1) with hj | hj | hj
  · simp only [registerCoeff, Fin.le_def, Fin.ext_iff]
    rw [ite_eq_left hj.le, ite_eq_left (show j.val ≤ n by omega),
      ite_eq_right (Nat.ne_of_lt hj), add_zero]
    unfold prodA
    rw [Finset.prod_Ico_succ_top (by omega), dite_eq_left hn, mul_comm]
  · have : j = ⟨n + 1, hn⟩ := Fin.ext hj
    subst j
    simp [registerCoeff, show ¬ (n + 1 ≤ n) by omega]
  · simp [registerCoeff, Fin.le_def, Fin.ext_iff, Nat.ne_of_gt hj,
      show ¬ j.val ≤ n + 1 from not_le.mpr hj, show ¬ j.val ≤ n by omega]

/-- The increment register as a finite linear combination of columns. -/
def register (ls : LowStorage s R) (u : Fin s → R) (i : Fin s) : R :=
  ∑ j, ls.registerCoeff i j * u j

private theorem register_zero (ls : LowStorage s R) (u : Fin s → R) (hs : 0 < s) :
    ls.register u ⟨0, hs⟩ = u ⟨0, hs⟩ := by
  classical
  simp [register, registerCoeff_zero]

private theorem register_succ (ls : LowStorage s R) (u : Fin s → R)
    (n : ℕ) (hn : n + 1 < s) :
    ls.register u ⟨n + 1, hn⟩ =
      ls.A ⟨n + 1, hn⟩ * ls.register u ⟨n, by omega⟩ + u ⟨n + 1, hn⟩ := by
  classical
  simp [register, registerCoeff_succ, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem slope_eq_register (ls : LowStorage s R) (u : Fin s → R) (i : Fin s) :
    ls.slope u i = ls.B i * ls.register u i := by
  simp [register, beta_eq_mul_registerCoeff, Finset.mul_sum, mul_assoc]

/-- The alternating column from equation (7) of the order-transfer proof. -/
def areaColumn (ls : LowStorage s R) (u v : Fin s → R) (i : Fin s) : R :=
  ls.pathPrefix u i * v i - ls.pathPrefix v i * u i

private theorem register_area (ls : LowStorage s R) (u v : Fin s → R)
    (n : ℕ) (hn : n < s) :
    ls.register (ls.areaColumn u v) ⟨n, hn⟩ =
      ls.pathPrefix u n * ls.register v ⟨n, hn⟩ -
        ls.pathPrefix v n * ls.register u ⟨n, hn⟩ := by
  induction n with
  | zero => simp [register_zero, areaColumn]
  | succ n ih =>
      rw [register_succ, ih (by omega), register_succ, register_succ]
      simp only [areaColumn, prefix_succ]
      rw [slope_eq_register ls u ⟨n, by omega⟩, slope_eq_register ls v ⟨n, by omega⟩]
      ring

/-- The signed area integrand is itself a coefficient-path increment. -/
theorem slope_area (ls : LowStorage s R) (u v : Fin s → R) (n : ℕ) :
    ls.slope (ls.areaColumn u v) n =
      ls.pathPrefix u n * ls.slope v n - ls.pathPrefix v n * ls.slope u n := by
  by_cases hn : n < s
  · rw [slope_eq_register ls _ ⟨n, hn⟩, register_area,
      slope_eq_register ls v ⟨n, hn⟩, slope_eq_register ls u ⟨n, hn⟩]
    ring
  · simp [slope, hn]

/-- The coefficient path on a straight segment. -/
def coefficientPath (ls : LowStorage s R) (u : Fin s → R) (n : ℕ) (θ : R) : R :=
  ls.pathPrefix u n + θ * ls.slope u n

/-- The area integrand is constant along each straight segment. -/
theorem coefficientPath_area_integrand (ls : LowStorage s R) (u v : Fin s → R)
    (n : ℕ) (θ : R) :
    ls.coefficientPath u n θ * ls.slope v n -
      ls.coefficientPath v n θ * ls.slope u n = ls.slope (ls.areaColumn u v) n := by
  rw [slope_area]
  unfold coefficientPath
  ring

/-- Accumulated signed area, including the current straight segment. -/
def coefficientArea (ls : LowStorage s R) (u v : Fin s → R) (n : ℕ) (θ : R) : R :=
  (∑ i : Fin s, if i.val < n then
    ls.pathPrefix u i * ls.slope v i - ls.pathPrefix v i * ls.slope u i else 0) +
    θ * (ls.pathPrefix u n * ls.slope v n - ls.pathPrefix v n * ls.slope u n)

/-- Area closure holds at every point, including when coefficients vanish. -/
theorem coefficientPath_area (ls : LowStorage s R) (u v : Fin s → R)
    (n : ℕ) (θ : R) :
    ls.coefficientArea u v n θ = ls.coefficientPath (ls.areaColumn u v) n θ := by
  unfold coefficientArea coefficientPath
  simp_rw [← slope_area]
  simp only [slope_coe, pathPrefix]

open HopfAlgebras in
/-- The grafting identity (equation (7)): areas of elementary columns
are differences of elementary columns, with no restriction on tree order. -/
theorem areaColumn_stageWeight (ls : LowStorage s R)
    (σ τ : List PTree) :
    ls.areaColumn (stageWeight ls.toRK (.node σ)) (stageWeight ls.toRK (.node τ)) =
      fun i => stageWeight ls.toRK (.node (.node σ :: τ)) i -
        stageWeight ls.toRK (.node (.node τ :: σ)) i := by
  funext i
  simp only [areaColumn, prefix_eq_A, stageWeight_node, stageWeightList_cons]

end BSeries.RungeKutta.LowStorage
