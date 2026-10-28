/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.ForwardBackward
import BSeries.Algebra.BandedMatrix
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The regular Krylov basis of an explicit tableau

The chain stage vectors form a lower triangular basis when the subdiagonal is nonzero. Vanishing chain moments make powers of the output functional select individual Krylov coordinates, as in Steps 1–2 of the Williamson proof.

Coordinates are a Mathlib linear equivalence, and change of basis for operators is its induced algebra equivalence. Both require a nonzero determinant; linearity, algebra laws, and inverse cancellation use the standard equivalence API.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] {s : ℕ}

/-- The columns are `𝟙, A𝟙, …, A^(s-1)𝟙`, expressed by chain stage weights. -/
def krylovMatrix (rk : RungeKutta (Fin s) R) : Matrix (Fin s) (Fin s) R :=
  fun i j => stageWeight rk (PTree.tallTree j.val) i

/-- The linear equivalence from stage vectors to coefficients in the regular chain basis. -/
def krylovCoordinates (rk : RungeKutta (Fin s) R) (hdet : rk.krylovMatrix.det ≠ 0) :
    (Fin s → R) ≃ₗ[R] (Fin s → R) :=
  (rk.krylovMatrix.toLinearEquiv'
    (rk.krylovMatrix.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet))).symm

theorem krylovMatrix_isLowerTriangular {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) : rk.krylovMatrix.IsLowerTriangular := by
  intro i j hij
  exact stageWeight_tallTree_eq_zero_of_lt hexp j.val i hij

theorem krylovMatrix_diag_ne_zero {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0) (i : Fin s) :
    rk.krylovMatrix i i ≠ 0 := by
  change stageWeight rk (PTree.tallTree i.val) ⟨i.val, i.isLt⟩ ≠ 0
  rw [stageWeight_tallTree_pivot hexp i.val i.isLt]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hsub _ _ rfl

theorem det_krylovMatrix_ne_zero {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0) :
    rk.krylovMatrix.det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (krylovMatrix_isLowerTriangular hexp)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => krylovMatrix_diag_ne_zero hexp hsub i

/-- A chain vector is one column of the Krylov basis. -/
theorem krylovCoordinates_tallTree {rk : RungeKutta (Fin s) R}
    (hdet : rk.krylovMatrix.det ≠ 0) (k : ℕ) (hk : k < s) (i : Fin s) :
    rk.krylovCoordinates hdet (stageWeight rk (PTree.tallTree k)) i =
      if i.val = k then 1 else 0 := by
  change (rk.krylovMatrix⁻¹ * rk.krylovMatrix) i ⟨k, hk⟩ = _
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)]
  simp only [Matrix.one_apply, Fin.ext_iff]

/-- Change of coordinates for stage operators, bundled so Mathlib supplies all algebra laws. -/
def inKrylovBasis (rk : RungeKutta (Fin s) R) (hdet : rk.krylovMatrix.det ≠ 0) :
    Matrix (Fin s) (Fin s) R ≃ₐ[R] Matrix (Fin s) (Fin s) R :=
  Matrix.toLinAlgEquiv' |>.trans ((rk.krylovCoordinates hdet).conjAlgEquiv R) |>.trans
    LinearMap.toMatrixAlgEquiv'

theorem inKrylovBasis_apply (rk : RungeKutta (Fin s) R)
    (hdet : rk.krylovMatrix.det ≠ 0) (M : Matrix (Fin s) (Fin s) R) (i j : Fin s) :
    rk.inKrylovBasis hdet M i j =
      rk.krylovCoordinates hdet (M *ᵥ stageWeight rk (PTree.tallTree j.val)) i := by
  change (rk.krylovMatrix⁻¹ *ᵥ (M *ᵥ (rk.krylovMatrix *ᵥ Pi.single j 1))) i = _
  rw [mulVec_single_one]
  rfl

/-- Initial zero coordinates in a stage vector force the same initial zero coordinates in its Krylov expansion. -/
theorem krylovCoordinates_eq_zero_of_lt {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    {v : Fin s → R} {k : ℕ} (hv : ∀ i : Fin s, i.val < k → v i = 0)
    (i : Fin s) (hi : i.val < k) : rk.krylovCoordinates hdet v i = 0 := by
  let := rk.krylovMatrix.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)
  have htri := Matrix.blockTriangular_inv_of_blockTriangular (krylovMatrix_isLowerTriangular hexp)
  change ∑ j, rk.krylovMatrix⁻¹ i j * v j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < k
  · rw [hv j hj, mul_zero]
  · rw [htri (by change i.val < j.val; omega), zero_mul]

/-- Powers of the output functional select the reverse-ordered Krylov coordinates. -/
theorem moment_eq_krylovCoordinate {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    (hmom : ∀ n : ℕ, n < s - 1 → weight rk (PTree.tallTree n) = 0)
    (v : Fin s → R) (l : ℕ) (hl : l < s) :
    rk.b ⬝ᵥ (rk.stageMatrix ^ l *ᵥ v) =
      weight rk (PTree.tallTree (s - 1)) *
        rk.krylovCoordinates hdet v ⟨s - 1 - l, by omega⟩ := by
  let j₀ : Fin s := ⟨s - 1 - l, by omega⟩
  have hentry (j : Fin s) : (rk.b ᵥ* rk.stageMatrix ^ l ᵥ* rk.krylovMatrix) j =
      weight rk (PTree.tallTree (l + j.val)) := by
    change (rk.b ᵥ* rk.stageMatrix ^ l) ⬝ᵥ stageWeight rk (PTree.tallTree j.val) = _
    rw [← dotProduct_mulVec, stageWeight_tallTree_eq_mulVec, mulVec_mulVec,
      ← pow_add, ← stageWeight_tallTree_eq_mulVec]
    rfl
  calc
    rk.b ⬝ᵥ (rk.stageMatrix ^ l *ᵥ v) =
        (rk.b ᵥ* rk.stageMatrix ^ l ᵥ* rk.krylovMatrix) ⬝ᵥ rk.krylovCoordinates hdet v := by
      rw [← dotProduct_mulVec, ← dotProduct_mulVec]
      exact congrArg (fun w => rk.b ⬝ᵥ (rk.stageMatrix ^ l *ᵥ w))
        ((rk.krylovCoordinates hdet).symm_apply_apply v).symm
    _ = _ := by
      unfold dotProduct
      rw [Finset.sum_eq_single j₀, hentry,
        show l + j₀.val = s - 1 by dsimp [j₀]; omega]
      · intro j _ hj
        rw [hentry]
        by_cases hjlt : l + j.val < s - 1
        · rw [hmom _ hjlt, zero_mul]
        · rw [weight_tallTree_eq_zero hexp _ (by
            have : j.val ≠ s - 1 - l := fun heq => hj (Fin.ext heq)
            omega), zero_mul]
      · simp

/-- Broom conditions eliminate all but the first two possible Krylov coordinates of `diag(c) A^k 𝟙`. -/
theorem krylovCoordinates_diagonal_eq_zero {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hdet : rk.krylovMatrix.det ≠ 0)
    (hmom : ∀ n : ℕ, n < s - 1 → weight rk (PTree.tallTree n) = 0)
    (htop : weight rk (PTree.tallTree (s - 1)) ≠ 0)
    (hbroom : ∀ k l : ℕ, 0 < k → k + 2 + l < s →
      rk.b ⬝ᵥ (rk.stageMatrix ^ l *ᵥ
        (diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k))) = 0)
    (k : ℕ) (hk : 0 < k) (j : Fin s) (hj : j.val < k ∨ k + 1 < j.val) :
    rk.krylovCoordinates hdet (diagonal rk.abscissa *ᵥ
      stageWeight rk (PTree.tallTree k)) j = 0 := by
  rcases hj with hj | hj
  · apply krylovCoordinates_eq_zero_of_lt hexp hdet (k := k) _ j hj
    intro i hi
    rw [mulVec_diagonal, stageWeight_tallTree_eq_zero_of_lt hexp k i hi, mul_zero]
  · let l := s - 1 - j.val
    have hl : l < s := by dsimp [l]; have := j.isLt; omega
    have heq := moment_eq_krylovCoordinate hexp hdet hmom
      (diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k)) l hl
    rw [hbroom k l hk (by dsimp [l]; have := j.isLt; omega)] at heq
    have hindex : (⟨s - 1 - l, by omega⟩ : Fin s) = j := by
      apply Fin.ext
      dsimp [l]
      have := j.isLt
      omega
    rw [hindex] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left htop

/-- The triangular pivot fixes the diagonal coefficient in the multiplication operator. -/
theorem krylovCoordinates_diagonal_self {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (hdet : rk.krylovMatrix.det ≠ 0) (k : Fin s) :
    rk.krylovCoordinates hdet (diagonal rk.abscissa *ᵥ
      stageWeight rk (PTree.tallTree k.val)) k = rk.abscissa k := by
  let v := diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k.val)
  have hrep := congrFun
    ((rk.krylovCoordinates hdet).symm_apply_apply v) k
  change (∑ j, rk.krylovMatrix k j * rk.krylovCoordinates hdet v j) = _ at hrep
  rw [Finset.sum_eq_single k] at hrep
  · apply mul_left_cancel₀ (krylovMatrix_diag_ne_zero hexp hsub k)
    rw [hrep]
    change (diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k.val)) k = _
    rw [mulVec_diagonal, mul_comm]
    rfl
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [krylovCoordinates_eq_zero_of_lt hexp hdet (k := k.val) _ j hj, mul_zero]
      intro i hi
      dsimp [v]
      rw [mulVec_diagonal, stageWeight_tallTree_eq_zero_of_lt hexp k.val i hi, mul_zero]
    · rw [krylovMatrix_isLowerTriangular hexp hj, zero_mul]
  · simp

/-- In the regular chain basis, multiplication by the abscissae is lower bidiagonal. This includes the penultimate column, for which support alone suffices. -/
theorem exists_diagonal_stageWeight_tallTree {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (hmom : ∀ n : ℕ, n < s - 1 → weight rk (PTree.tallTree n) = 0)
    (htop : weight rk (PTree.tallTree (s - 1)) ≠ 0)
    (hbroom : ∀ k l : ℕ, 0 < k → k + 2 + l < s →
      rk.b ⬝ᵥ (rk.stageMatrix ^ l *ᵥ
        (diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k))) = 0)
    (k : Fin s) (hk : k.val + 1 < s) :
    ∃ t : R, ∀ i : Fin s,
      rk.abscissa i * stageWeight rk (PTree.tallTree k.val) i =
        rk.abscissa k * stageWeight rk (PTree.tallTree k.val) i +
          t * stageWeight rk (PTree.tallTree (k.val + 1)) i := by
  have hdet := det_krylovMatrix_ne_zero hexp hsub
  by_cases hk0 : k.val = 0
  · refine ⟨1, ?_⟩
    have hc : rk.abscissa k = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hexp k j (by simp only [Fin.le_def, hk0]; exact Nat.zero_le _)
    intro i
    rw [hc]
    simp [hk0, PTree.tallTree, stageWeightList, abscissa]
  · let k₁ : Fin s := ⟨k.val + 1, hk⟩
    let v := diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree k.val)
    let u := rk.krylovCoordinates hdet v
    refine ⟨u k₁, ?_⟩
    have hv : v = rk.abscissa k • stageWeight rk (PTree.tallTree k.val) +
        u k₁ • stageWeight rk (PTree.tallTree (k.val + 1)) := by
      apply (rk.krylovCoordinates hdet).injective
      ext j
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        krylovCoordinates_tallTree hdet k.val k.isLt,
        krylovCoordinates_tallTree hdet (k.val + 1) hk]
      by_cases hj : j = k
      · subst j
        simp only [ite_true, ite_eq_right (by omega : k.val ≠ k.val + 1),
          mul_one, mul_zero, add_zero]
        exact krylovCoordinates_diagonal_self hexp hsub hdet k
      · have hne : j.val ≠ k.val := fun h => hj (Fin.ext h)
        rw [ite_eq_right hne, mul_zero, zero_add]
        by_cases hj₁ : j.val = k.val + 1
        · have heq : j = k₁ := Fin.ext hj₁
          rw [ite_eq_left hj₁, mul_one, heq]
        · rw [ite_eq_right hj₁, mul_zero]
          apply krylovCoordinates_diagonal_eq_zero hexp hdet hmom htop hbroom k.val (by omega) j
          omega
    intro i
    simpa only [v, mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hv i

/-- The final Krylov vector is supported only at the final stage, so its diagonal multiplication has no next-column term. -/
theorem diagonal_stageWeight_tallTree_last {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hs : 0 < s) (i : Fin s) :
    rk.abscissa i * stageWeight rk (PTree.tallTree (s - 1)) i =
      rk.abscissa ⟨s - 1, by omega⟩ * stageWeight rk (PTree.tallTree (s - 1)) i := by
  by_cases hi : i.val = s - 1
  · have heq : i = (⟨s - 1, by omega⟩ : Fin s) := Fin.ext hi
    rw [heq]
  · rw [stageWeight_tallTree_eq_zero_of_lt hexp (s - 1) i (by have := i.isLt; omega),
      mul_zero, mul_zero]

/-- The coefficient form of a lower bidiagonal multiplication operator in the chain basis. -/
def IsKrylovBidiagonal (rk : RungeKutta (Fin s) R) (t : Fin (s - 1) → R) : Prop :=
  ∀ (k : Fin (s - 1)) (i : Fin s),
    rk.abscissa i * stageWeight rk (PTree.tallTree k.val) i =
      rk.abscissa ⟨k.val, by have := k.isLt; omega⟩ *
          stageWeight rk (PTree.tallTree k.val) i +
        t k * stageWeight rk (PTree.tallTree (k.val + 1)) i

/-- The first off-diagonal coefficient is one, since `diag(c)𝟙 = A𝟙`. -/
theorem IsKrylovBidiagonal.first_eq_one {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t) :
    t ⟨0, by omega⟩ = 1 := by
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  have hc₀ : rk.abscissa i₀ = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact hexp i₀ j (by change 0 ≤ j.val; omega)
  have hc₁ : rk.abscissa i₁ ≠ 0 := by
    have h := krylovMatrix_diag_ne_zero hexp hsub i₁
    simpa [krylovMatrix, i₁, PTree.tallTree, stageWeightList, abscissa] using h
  have h := ht ⟨0, by omega⟩ i₁
  change rk.abscissa i₁ * stageWeight rk (PTree.tallTree 0) i₁ =
    rk.abscissa i₀ * stageWeight rk (PTree.tallTree 0) i₁ +
      t ⟨0, by omega⟩ * stageWeight rk (PTree.tallTree 1) i₁ at h
  rw [hc₀] at h
  have h' : rk.abscissa i₁ = t ⟨0, by omega⟩ * rk.abscissa i₁ := by
    simpa [PTree.tallTree, stageWeightList, abscissa] using h
  exact mul_right_cancel₀ hc₁ (h'.symm.trans (one_mul _).symm)

/-- Extend the subdiagonal by zero at both boundaries. The value at `k + 1` is the coefficient denoted `t_k` in the proof. -/
def krylovSubdiagonal (t : Fin (s - 1) → R) (k : ℕ) : R :=
  if hk : 0 < k ∧ k < s then t ⟨k - 1, by omega⟩ else 0

@[simp] theorem krylovSubdiagonal_zero (t : Fin (s - 1) → R) :
    krylovSubdiagonal t 0 = 0 := by simp [krylovSubdiagonal]

@[simp] theorem krylovSubdiagonal_end (t : Fin (s - 1) → R) :
    krylovSubdiagonal t s = 0 := by simp [krylovSubdiagonal]

theorem krylovSubdiagonal_succ (t : Fin (s - 1) → R) (k : ℕ) (hk : k + 1 < s) :
    krylovSubdiagonal t (k + 1) = t ⟨k, by omega⟩ := by
  unfold krylovSubdiagonal
  rw [dite_eq_left (show 0 < k + 1 ∧ k + 1 < s from ⟨by omega, hk⟩)]
  rfl

/-- The bidiagonal relation expresses chain vectors in the Newton polynomial basis of the nodes. -/
theorem IsKrylovBidiagonal.node_product {rk : RungeKutta (Fin s) R}
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (k : ℕ) (hk : k < s) (i : Fin s) :
    (∏ j : Fin k, (rk.abscissa i - rk.abscissa ⟨j.val, by have := j.isLt; omega⟩)) =
      (∏ j : Fin k, krylovSubdiagonal t (j.val + 1)) *
        stageWeight rk (PTree.tallTree k) i := by
  induction k with
  | zero => simp [PTree.tallTree, stageWeightList]
  | succ k ih =>
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih (by omega), krylovSubdiagonal_succ t k hk]
      linear_combination (∏ j : Fin k, krylovSubdiagonal t (j.val + 1)) *
        ht ⟨k, by omega⟩ i

/-- A zero lowering coefficient confines all nodes to the preceding ones. -/
theorem IsKrylovBidiagonal.card_nodes_le_of_eq_zero [DecidableEq R]
    {rk : RungeKutta (Fin s) R} {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (k : Fin (s - 1)) (hk : t k = 0) :
    (Finset.univ.image rk.abscissa).card ≤ k.val + 1 := by
  classical
  have hsub : Finset.univ.image rk.abscissa ⊆
      Finset.univ.image (fun j : Fin (k.val + 1) =>
        rk.abscissa ⟨j.val, by have := j.isLt; have := k.isLt; omega⟩) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have h := ht.node_product (k.val + 1) (by have := k.isLt; omega) i
    have hz : (∏ j : Fin (k.val + 1), krylovSubdiagonal t (j.val + 1)) = 0 := by
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨Fin.last k.val, Finset.mem_univ _, ?_⟩
      simpa only [Fin.val_last, krylovSubdiagonal_succ t k.val (by have := k.isLt; omega)] using hk
    rw [hz, zero_mul] at h
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (sub_eq_zero.mp hj).symm⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa using (Finset.card_image_le (f := fun j : Fin (k.val + 1) =>
      rk.abscissa ⟨j.val, by have := j.isLt; have := k.isLt; omega⟩) (s := Finset.univ)))

/-- Entries of the lower bidiagonal multiplication operator, including its truncated final column. -/
theorem IsKrylovBidiagonal.inKrylovBasis_diagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t) (i j : Fin s) :
    rk.inKrylovBasis hdet (diagonal rk.abscissa) i j =
      (if i = j then rk.abscissa j else 0) +
        (if i.val = j.val + 1 then krylovSubdiagonal t (j.val + 1) else 0) := by
  rw [inKrylovBasis_apply]
  by_cases hj : j.val + 1 < s
  · have hcol : diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree j.val) =
        rk.abscissa j • stageWeight rk (PTree.tallTree j.val) +
          t ⟨j.val, by omega⟩ • stageWeight rk (PTree.tallTree (j.val + 1)) := by
      ext l
      simpa only [mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        ht ⟨j.val, by omega⟩ l
    rw [hcol, map_add, map_smul, map_smul]
    change rk.abscissa j * rk.krylovCoordinates hdet (stageWeight rk (PTree.tallTree j.val)) i +
      t ⟨j.val, by omega⟩ * rk.krylovCoordinates hdet (stageWeight rk (PTree.tallTree (j.val + 1))) i = _
    rw [krylovCoordinates_tallTree hdet j.val j.isLt,
      krylovCoordinates_tallTree hdet (j.val + 1) hj, krylovSubdiagonal_succ t j.val hj]
    simp only [mul_ite, mul_one, mul_zero, Fin.ext_iff]
  · have hjlast : j.val = s - 1 := by have := j.isLt; omega
    have hcol : diagonal rk.abscissa *ᵥ stageWeight rk (PTree.tallTree j.val) =
        rk.abscissa j • stageWeight rk (PTree.tallTree j.val) := by
      ext l
      have h := diagonal_stageWeight_tallTree_last hexp (by have := j.isLt; omega) l
      have heq : (⟨s - 1, by have := j.isLt; omega⟩ : Fin s) = j := Fin.ext hjlast.symm
      simpa only [heq, hjlast, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using h
    rw [hcol, map_smul]
    change rk.abscissa j * rk.krylovCoordinates hdet (stageWeight rk (PTree.tallTree j.val)) i = _
    rw [krylovCoordinates_tallTree hdet j.val j.isLt,
      ite_eq_right (by have := i.isLt; omega : i.val ≠ j.val + 1), add_zero]
    simp only [mul_ite, mul_one, mul_zero, Fin.ext_iff]

/-- The multiplication operator is precisely the lower band matrix with extended boundary coefficients. -/
theorem IsKrylovBidiagonal.eq_lowerBand {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (c : ℕ → R) (hc : ∀ i : Fin s, c i.val = rk.abscissa i) :
    rk.inKrylovBasis hdet (diagonal rk.abscissa) = lowerBand s c (krylovSubdiagonal t) := by
  ext i j
  rw [ht.inKrylovBasis_diagonal hexp hdet]
  simp only [lowerBand, hc]
  split_ifs with hij hnext hnext
  · subst j
    omega
  · subst j; rfl
  · rw [hnext]
  · rfl

/-- Right multiplication by the bidiagonal operator uses only two entries of each row. -/
theorem IsKrylovBidiagonal.mul_inKrylovBasis_diagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (M : Matrix (Fin s) (Fin s) R) (i j : Fin s) :
    (M * rk.inKrylovBasis hdet (diagonal rk.abscissa)) i j =
      M i j * rk.abscissa j +
        if hj : j.val + 1 < s then M i ⟨j.val + 1, hj⟩ *
          krylovSubdiagonal t (j.val + 1) else 0 := by
  rw [ht.eq_lowerBand hexp hdet (fun k => if hk : k < s then rk.abscissa ⟨k, hk⟩ else 0)
    (fun i => dite_eq_left i.isLt), Matrix.mul_lowerBand, dite_eq_left j.isLt]

/-- Left multiplication by the bidiagonal operator uses only two entries of each column. -/
theorem IsKrylovBidiagonal.inKrylovBasis_diagonal_mul {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    {t : Fin (s - 1) → R} (ht : IsKrylovBidiagonal rk t)
    (M : Matrix (Fin s) (Fin s) R) (i j : Fin s) :
    (rk.inKrylovBasis hdet (diagonal rk.abscissa) * M) i j =
      rk.abscissa i * M i j +
        if hi : 0 < i.val then krylovSubdiagonal t i.val *
          M ⟨i.val - 1, by have := i.isLt; omega⟩ j else 0 := by
  rw [ht.eq_lowerBand hexp hdet (fun k => if hk : k < s then rk.abscissa ⟨k, hk⟩ else 0)
    (fun i => dite_eq_left i.isLt), Matrix.lowerBand_mul, dite_eq_left i.isLt]

variable [CharZero R] [Invertible (2 : R)]

/-- The bidiagonal multiplication relation for the actual forward--backward tableau, with no nonvanishing assumption on its off-diagonal coefficients. -/
theorem exists_forwardBackward_bidiagonal {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    ∃ t : Fin (s + s - 1) → R,
      IsKrylovBidiagonal rk.forwardBackward t ∧ t ⟨0, by omega⟩ = 1 := by
  have hexpc := isExplicit_forwardBackward rk hexp
  have hsub := forwardBackward_subdiagonal_ne_zero (by omega : 0 < s) hexp hcons hanti
  have hmom (n : ℕ) (hn : n < s + s - 1) :
      weight rk.forwardBackward (PTree.tallTree n) = 0 :=
    weight_forwardBackward_eq_zero hanti _ (by rw [PTree.order_tallTree]; omega)
  have htop : weight rk.forwardBackward (PTree.tallTree (s + s - 1)) ≠ 0 := by
    change stabilityCoeff rk.forwardBackward (s + s - 1 + 1) ≠ 0
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s + s)]
    exact stabilityCoeff_forwardBackward_last_ne_zero (by omega) hexp hcons hanti
  have hbroom (k l : ℕ) (hk : 0 < k) (hkl : k + 2 + l < s + s) :
      rk.forwardBackward.b ⬝ᵥ (rk.forwardBackward.stageMatrix ^ l *ᵥ
        (diagonal rk.forwardBackward.abscissa *ᵥ stageWeight rk.forwardBackward (PTree.tallTree k))) = 0 := by
    rw [stageWeight_tallTree_eq_mulVec]
    have h := forwardBackward_broom_moment hanti (k - 1) l (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using h
  have h (k : Fin (s + s - 1)) := exists_diagonal_stageWeight_tallTree
    hexpc hsub hmom htop hbroom ⟨k.val, by have := k.isLt; omega⟩
      (by change k.val + 1 < s + s; have := k.isLt; omega)
  choose t ht using h
  exact ⟨t, ht, IsKrylovBidiagonal.first_eq_one (by omega) hexpc hsub ht⟩

end

end BSeries.RungeKutta
