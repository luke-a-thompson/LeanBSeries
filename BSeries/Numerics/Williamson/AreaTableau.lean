import BSeries.Numerics.Williamson.Basic
import BSeries.Numerics.Williamson.Area

/-! # The area-closed path of the existing Williamson tableau -/

namespace BSeries.RungeKutta.LowStorage

open scoped BigOperators
open WilliamsonPath

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Extend a finite column by zero. -/
def extend (u : Fin s → R) (n : ℕ) : R :=
  if h : n < s then u ⟨n, h⟩ else 0

@[simp] theorem extend_coe (u : Fin s → R) (i : Fin s) : extend u i = u i := by
  simp [extend, i.isLt]

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
  · have hj' : ¬ j ≤ (⟨0, hs⟩ : Fin s) := by
      intro h; apply hj; apply Fin.ext; change j.val ≤ 0 at h; change j.val = 0; omega
    simp [registerCoeff, hj, hj']

private theorem registerCoeff_succ (ls : LowStorage s R) (n : ℕ)
    (hn : n + 1 < s) (j : Fin s) :
    ls.registerCoeff ⟨n + 1, hn⟩ j =
      ls.A ⟨n + 1, hn⟩ * ls.registerCoeff ⟨n, by omega⟩ j +
        if j = ⟨n + 1, hn⟩ then 1 else 0 := by
  by_cases hj : j.val ≤ n
  · have h₁ : j ≤ (⟨n, by omega⟩ : Fin s) := hj
    have h₂ : j ≤ (⟨n + 1, hn⟩ : Fin s) := by exact Nat.le_succ_of_le hj
    have h₃ : j ≠ (⟨n + 1, hn⟩ : Fin s) := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp only [registerCoeff, ite_eq_left h₁, ite_eq_left h₂, ite_eq_right h₃, add_zero]
    unfold prodA
    rw [Finset.prod_Ico_succ_top (by omega), dite_eq_left hn]
    ring
  · by_cases heq : j = ⟨n + 1, hn⟩
    · subst j
      simp [registerCoeff, show ¬ (n + 1 ≤ n) by omega]
    · have h₁ : ¬ j ≤ (⟨n, by omega⟩ : Fin s) := hj
      have h₂ : ¬ j ≤ (⟨n + 1, hn⟩ : Fin s) := by
        intro h
        apply heq
        apply Fin.ext
        change j.val ≤ n + 1 at h
        dsimp
        omega
      simp [registerCoeff, h₁, h₂, heq]

/-- The recurrence register agrees with the unrolled tableau coefficients. -/
theorem register_eq_sum (ls : LowStorage s R) (u : Fin s → R)
    (n : ℕ) (hn : n < s) :
    register (extend ls.A) (extend u) (n + 1) =
      ∑ j, ls.registerCoeff ⟨n, hn⟩ j * u j := by
  classical
  induction n with
  | zero =>
      simp [register, extend, hn, registerCoeff_zero]
  | succ n ih =>
      rw [register, ih (by omega)]
      simp only [extend, dite_eq_left hn]
      simp_rw [registerCoeff_succ ls n hn, add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp [mul_assoc]

/-- A scalar increment of the coefficient path is the corresponding `beta` row. -/
theorem increment_eq_sum_beta (ls : LowStorage s R) (u : Fin s → R)
    (i : Fin s) :
    extend ls.B i * register (extend ls.A) (extend u) (i.val + 1) =
      ∑ j, ls.beta i j * u j := by
  rw [extend_coe, register_eq_sum ls u i i.isLt, Finset.mul_sum]
  simp_rw [beta_eq_mul_registerCoeff, mul_assoc]

/-- The recurrence prefix is the sum of the unrolled exponential increments. -/
theorem endpoint_eq_sum (ls : LowStorage s R) (u : Fin s → R)
    (n : ℕ) (hn : n ≤ s) :
    endpoint (extend ls.A) (extend ls.B) (extend u) n =
      ∑ i : Fin s, if i.val < n then ∑ j, ls.beta i j * u j else 0 := by
  classical
  induction n with
  | zero => simp [endpoint]
  | succ n ih =>
      have hn' : n < s := by omega
      rw [endpoint, ih (by omega), increment_eq_sum_beta ls u ⟨n, hn'⟩]
      have hsplit : ∀ i : Fin s,
          (if i.val < n + 1 then ∑ j, ls.beta i j * u j else 0) =
          (if i.val < n then ∑ j, ls.beta i j * u j else 0) +
            (if i = ⟨n, hn'⟩ then ∑ j, ls.beta i j * u j else 0) := by
        intro i
        by_cases hi : i.val < n
        · have hne : i ≠ (⟨n, hn'⟩ : Fin s) := by
            intro h; have := congrArg Fin.val h; dsimp at this; omega
          simp [hi, hne, show i.val < n + 1 by omega]
        · by_cases heq : i = ⟨n, hn'⟩
          · subst i; simp
          · have hgt : ¬ i.val < n + 1 := by
              intro h; apply heq; apply Fin.ext; dsimp; omega
            simp [hi, heq, hgt]
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
      simp

/-- Prefixes of the coefficient path are exactly the rows of `toRK`. -/
theorem endpoint_eq_toRK_A (ls : LowStorage s R) (u : Fin s → R) (i : Fin s) :
    endpoint (extend ls.A) (extend ls.B) (extend u) i =
      ∑ j, ls.toRK.A i j * u j := by
  rw [endpoint_eq_sum ls u i i.isLt.le]
  simp_rw [toRK_A, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]

/-- The final endpoint is the output row `b` of `toRK`. -/
theorem endpoint_eq_toRK_b (ls : LowStorage s R) (u : Fin s → R) :
    endpoint (extend ls.A) (extend ls.B) (extend u) s =
      ∑ j, ls.toRK.b j * u j := by
  rw [endpoint_eq_sum ls u s le_rfl]
  simp only [Fin.isLt, ite_true]
  simp_rw [toRK_b, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The alternating column `D_A(u,v)` for the induced tableau. -/
def areaColumn (ls : LowStorage s R) (u v : Fin s → R) (i : Fin s) : R :=
  (∑ j, ls.toRK.A i j * u j) * v i -
    (∑ j, ls.toRK.A i j * v j) * u i

theorem extend_areaColumn (ls : LowStorage s R) (u v : Fin s → R) :
    extend (ls.areaColumn u v) =
      bracket (extend ls.A) (extend ls.B) (extend u) (extend v) := by
  funext n
  by_cases hn : n < s
  · change extend (ls.areaColumn u v) (⟨n, hn⟩ : Fin s) = _
    rw [extend_coe]
    simp only [bracket, areaColumn,
      endpoint_eq_toRK_A ls u ⟨n, hn⟩, endpoint_eq_toRK_A ls v ⟨n, hn⟩]
    simp [extend, hn]
  · simp [extend, bracket, hn]

/-- **Lemma 1 for `LowStorage.toRK`**: the area of any two scalar
projections of the coefficient path is the projection along `D_A(u,v)`.
The equality holds for every segment parameter, not just at the endpoint. -/
theorem coefficientPath_area (ls : LowStorage s R) (u v : Fin s → R)
    (n : ℕ) (θ : R) :
    segmentArea (extend ls.A) (extend ls.B) (extend u) (extend v) n θ =
      segment (extend ls.A) (extend ls.B) (extend (ls.areaColumn u v)) n θ := by
  rw [extend_areaColumn, area_eq]

open HopfAlgebras in
/-- The grafting identity (equation (7)): areas of elementary columns
are differences of elementary columns, with no restriction on tree order. -/
theorem areaColumn_stageWeight (ls : LowStorage s R)
    (σ τ : List PTree) :
    ls.areaColumn (stageWeight ls.toRK (.node σ)) (stageWeight ls.toRK (.node τ)) =
      fun i => stageWeight ls.toRK (.node (.node σ :: τ)) i -
        stageWeight ls.toRK (.node (.node τ :: σ)) i := by
  funext i
  simp only [areaColumn, stageWeight_node, stageWeightList_cons]

end BSeries.RungeKutta.LowStorage
