/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.ExactFlow
import BSeries.Numerics.Composition
import Mathlib.Data.Sum.Order

/-!
# Explicit and Effectively Symmetric (EES) Runge–Kutta schemes

Following arXiv:2507.21006, Section 8. The antisymmetric component of any
B-series method vanishes on forests of odd order (Proposition 8.2,
`prop:plus_zero`), so the antisymmetric order of a method is always odd or
infinite; a method is symmetric precisely when its antisymmetric component is
trivial at every order. An `EES(n, m)` scheme is an explicit Runge–Kutta
scheme of order exactly `n` and antisymmetric order exactly `m`.
-/

namespace BSeries

open HopfAlgebras

universe u v

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- **The antisymmetric component vanishes at odd orders**: `τ⁺ = 0` for
`|τ|` odd (arXiv:2507.21006, Proposition `plus_zero`), in functional form. -/
theorem antisymmetricPart_evalForest_of_odd_order (ψ : Character R)
    {φ : RootedForest} (hφ : Odd (RootedForest.order φ)) :
    LinearFunctional.evalForest (antisymmetricPart ψ) φ = 0 := by
  have h := congrArg (fun f : LinearFunctional R =>
    f (ofForest (R := R) φ)) (compGradingInvolution_antisymmetricPart ψ)
  simp only [LinearFunctional.compGradingInvolution_ofForest] at h
  rw [hφ.neg_one_pow, neg_one_mul] at h
  have h2 : (2 : R) * antisymmetricPart ψ (ofForest (R := R) φ) = 0 := by
    linear_combination -h
  have h3 := congrArg (fun r => ⅟(2 : R) * r) h2
  show antisymmetricPart ψ (ofForest (R := R) φ) = 0
  simpa [invOf_mul_cancel_left'] using h3

/-- A B-series method has antisymmetric order at least `m` if its
antisymmetric component agrees with the counit on all forests of order at
most `m`, i.e. `ψ(τ⁺) = 0` for `1 ≤ |τ| ≤ m`
(arXiv:2507.21006, Definition 8.1). -/
def HasAntisymOrder (ψ : Character R) (m : ℕ) : Prop :=
  LinearFunctional.AgreeUpToOrder (antisymmetricPart ψ)
    (LinearFunctional.counit R) m

theorem HasAntisymOrder.mono {ψ : Character R} {k m : ℕ}
    (h : HasAntisymOrder ψ m) (hkm : k ≤ m) : HasAntisymOrder ψ k :=
  LinearFunctional.AgreeUpToOrder.mono h hkm

/-- **The antisymmetric order is odd (or infinite)**: since `τ⁺ = 0` at odd
orders, antisymmetric order at an even `m` extends automatically to `m + 1`
(arXiv:2507.21006, Section 8). -/
theorem HasAntisymOrder.succ_of_even {ψ : Character R} {m : ℕ}
    (h : HasAntisymOrder ψ m) (hm : Even m) : HasAntisymOrder ψ (m + 1) := by
  intro φ hφ
  by_cases hle : RootedForest.order φ ≤ m
  · exact h φ hle
  push Not at hle
  have horder : RootedForest.order φ = m + 1 := le_antisymm hφ hle
  have hodd : Odd (RootedForest.order φ) := by
    rw [horder]
    exact Even.add_one hm
  have hne : φ ≠ 0 := by
    intro h0
    rw [h0, RootedForest.order_zero] at horder
    exact Nat.succ_ne_zero m horder.symm
  rw [antisymmetricPart_evalForest_of_odd_order ψ hodd,
    LinearFunctional.evalForest_counit]
  classical
  simp [ForestAlgebra.counitCoeff, hne]

/-- An odd (symmetric) character has trivial antisymmetric component. -/
theorem antisymmetricPart_of_isOdd {ψ : Character R} (h : IsOdd ψ) :
    antisymmetricPart ψ = LinearFunctional.counit R := by
  have hinv : involution ψ = inverseCharacter ψ := by
    apply linearFunctional_ofCharacter_injective
    rw [ofCharacter_inverseCharacter]
    exact h
  rw [antisymmetricPart, symmetricPart_of_isOdd h, ← ofCharacter_involution,
    hinv, ← linearFunctional_ofCharacter_convolution,
    convolution_inverseCharacter_right, linearFunctional_ofCharacter_unit]

/-- Symmetric methods have infinite antisymmetric order. -/
theorem hasAntisymOrder_of_isOdd {ψ : Character R} (h : IsOdd ψ) (m : ℕ) :
    HasAntisymOrder ψ m := by
  rw [HasAntisymOrder, antisymmetricPart_of_isOdd h]
  exact LinearFunctional.agreeUpToOrder_refl _ m

/-- A method with infinite antisymmetric order is symmetric. -/
theorem isOdd_of_forall_hasAntisymOrder {ψ : Character R}
    (h : ∀ m, HasAntisymOrder ψ m) : IsOdd ψ := by
  have hpart : antisymmetricPart ψ = LinearFunctional.counit R :=
    LinearFunctional.ext_evalForest fun φ =>
      h (RootedForest.order φ) φ le_rfl
  have hσ : symmetricPart ψ = LinearFunctional.ofCharacter ψ := by
    have hdec := convolution_antisymmetricPart_symmetricPart ψ
    rwa [hpart, LinearFunctional.convolution_counit_left] at hdec
  have hodd := convolution_compGradingInvolution_symmetricPart ψ
  rw [hσ, ← ofCharacter_involution, ← linearFunctional_ofCharacter_convolution,
    ← linearFunctional_ofCharacter_unit] at hodd
  have hchar : convolution (involution ψ) ψ = unit R :=
    linearFunctional_ofCharacter_injective hodd
  have hinv : involution ψ = inverseCharacter ψ :=
    convolution_inverse_unique hchar (convolution_inverseCharacter_right ψ)
  show LinearFunctional.ofCharacter (involution ψ) =
    LinearFunctional.compAntipode (LinearFunctional.ofCharacter ψ)
  rw [hinv, ofCharacter_inverseCharacter]

/-- **A B-series method is symmetric iff its antisymmetric order is
infinite** (arXiv:2507.21006, Section 8). -/
theorem isOdd_iff_forall_hasAntisymOrder (ψ : Character R) :
    IsOdd ψ ↔ ∀ m, HasAntisymOrder ψ m :=
  ⟨fun h m => hasAntisymOrder_of_isOdd h m, isOdd_of_forall_hasAntisymOrder⟩

end

end Character

end ForestAlgebra

namespace RungeKutta

variable {ι : Type u} {R : Type v}

/-- A Runge–Kutta tableau is explicit when its stage matrix is strictly lower
triangular with respect to a linear order on the stages. -/
def IsExplicit [LinearOrder ι] [Zero R] (rk : RungeKutta ι R) : Prop :=
  ∀ i j, i ≤ j → rk.A i j = 0

theorem IsExplicit.abscissa_zero [CommSemiring R] {s : ℕ}
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hs : 0 < s) :
    rk.abscissa ⟨0, hs⟩ = 0 :=
  Finset.sum_eq_zero fun j _ => hexp _ j (Nat.zero_le j.val)

theorem explicitEuler_isExplicit [Zero R] [One R] :
    IsExplicit (explicitEuler R) := by
  intro i j _
  rfl

/-- Composition preserves explicitness, ordering all first-block stages
before the second block (lexicographic order on the stages). -/
theorem isExplicit_compose {κ : Type u} [LinearOrder ι] [LinearOrder κ]
    [Zero R] {rk₁ : RungeKutta ι R} {rk₂ : RungeKutta κ R}
    (h₁ : IsExplicit rk₁) (h₂ : IsExplicit rk₂) :
    IsExplicit (ι := ι ⊕ₗ κ) (compose rk₁ rk₂) := by
  intro i j hij
  rcases i with a | a <;> rcases j with b | b
  · exact h₁ a b (Sum.Lex.inl_le_inl_iff.1 hij)
  · rfl
  · exact absurd hij Sum.Lex.not_inr_le_inl
  · exact h₂ a b (Sum.Lex.inr_le_inr_iff.1 hij)

/-- An **Explicit and Effectively Symmetric** scheme of order `n` and
antisymmetric order `m`: an explicit Runge–Kutta scheme with `ord(ψ) = n` and
`ord⁺(ψ) = m` (arXiv:2507.21006, Definition 8.2, the class `EES(n, m)`). -/
def IsEES [LinearOrder ι] [Fintype ι] [Field R] [Invertible (2 : R)]
    (rk : RungeKutta ι R) (n m : ℕ) : Prop :=
  IsExplicit rk ∧
  (HasOrder rk n ∧ ¬ HasOrder rk (n + 1)) ∧
  (ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) m ∧
    ¬ ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (m + 1))

/-- **The antisymmetric order of an EES scheme is odd**
(arXiv:2507.21006, Section 8): the class `EES(n, m)` is empty for even `m`. -/
theorem IsEES.odd_antisymOrder [LinearOrder ι] [Fintype ι] [Field R]
    [Invertible (2 : R)] {rk : RungeKutta ι R} {n m : ℕ}
    (h : IsEES rk n m) : Odd m := by
  rcases Nat.even_or_odd m with he | ho
  · exact absurd (h.2.2.1.succ_of_even he) h.2.2.2
  · exact ho

end RungeKutta

end BSeries

namespace BSeries

open HopfAlgebras

universe w

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type w}

/-- **The antisymmetric order dominates the order**: a method agreeing with
the exact solution up to order `n` has antisymmetric order at least `n`
(arXiv:2507.21006, Section 8: `ord⁺(ψ) ≥ ord(ψ)`). -/
theorem hasAntisymOrder_of_agree_exact [Field R] [CharZero R]
    [Invertible (2 : R)] {ψ : Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      ψ.evalForest φ =
        (Series.toCharacter (Series.exact R)).evalForest φ) :
    HasAntisymOrder ψ n := by
  set e : Character R := Series.toCharacter (Series.exact R) with he
  have hadj := Series.adjointCharacter_evalForest_congr h
  have hconv := Series.convolution_evalForest_congr hadj h
  have hσ := RootedForest.sqrtCoeff_congr n hconv
  -- the antisymmetric parts agree up to order n
  have hplus : LinearFunctional.AgreeUpToOrder (antisymmetricPart ψ)
      (antisymmetricPart e) n := by
    refine LinearFunctional.AgreeUpToOrder.convolution ?_ ?_
    · intro φ hφ
      exact h φ hφ
    · intro φ hφ
      rw [LinearFunctional.evalForest,
        LinearFunctional.compGradingInvolution_ofForest,
        LinearFunctional.evalForest,
        LinearFunctional.compGradingInvolution_ofForest,
        symmetricPart, sqrtFunctional_ofForest,
        symmetricPart, sqrtFunctional_ofForest, hσ φ hφ]
  intro φ hφ
  rw [hplus φ hφ, antisymmetricPart_of_isOdd
    (Series.isOdd_toCharacter_exact (R := R))]

/-- **The antisymmetric component detects the leading defect at even
orders**: if `ψ` agrees with the exact solution up to an odd order `m`,
then at order `m + 1` the antisymmetric component equals the defect of `ψ`.
Hence a method of order exactly `m` (`m` odd) has antisymmetric order
exactly `m` (arXiv:2507.21006, Section 8). -/
theorem antisymmetricPart_eval_first_defect [Field R] [CharZero R]
    [Invertible (2 : R)] {ψ : Character R} {m : ℕ} (hm : Odd m)
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ m →
      ψ.evalForest φ =
        (Series.toCharacter (Series.exact R)).evalForest φ)
    {τ : RootedForest} (hτ : RootedForest.order τ = m + 1) :
    antisymmetricPart ψ (ofForest (R := R) τ) =
      ψ.evalForest τ -
        (Series.toCharacter (Series.exact R)).evalForest τ := by
  classical
  set e : Character R := Series.toCharacter (Series.exact R) with he
  have hτne : τ ≠ 0 := (RootedForest.order_pos_iff_ne_zero τ).1 (by omega)
  have hadj := Series.adjointCharacter_evalForest_congr h
  have hconv := Series.convolution_evalForest_congr hadj h
  have hσ := RootedForest.sqrtCoeff_congr m hconv
  -- the square roots agree at order m + 1 as well: the defects cancel
  have hτσ := RootedForest.two_mul_sqrtCoeff_add_proper
    (convolution (adjointCharacter ψ) ψ) hτne
  have hτσe := RootedForest.two_mul_sqrtCoeff_add_proper
    (convolution (adjointCharacter e) e) hτne
  have hγψ := Series.convolution_evalForest_boundary_split
    (adjointCharacter ψ) ψ hτne
  have hγe := Series.convolution_evalForest_boundary_split
    (adjointCharacter e) e hτne
  rw [hγψ] at hτσ
  rw [hγe] at hτσe
  have hproper_σ : ((RootedForest.properCoproductTerms τ).map fun term =>
      RootedForest.sqrtCoeff (convolution (adjointCharacter ψ) ψ) term.1 *
      RootedForest.sqrtCoeff (convolution (adjointCharacter ψ) ψ) term.2).sum
      = ((RootedForest.properCoproductTerms τ).map fun term =>
      RootedForest.sqrtCoeff (convolution (adjointCharacter e) e) term.1 *
      RootedForest.sqrtCoeff (convolution (adjointCharacter e) e) term.2).sum
      := by
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    have hl : RootedForest.order term.1 ≤ m := by
      have := RootedForest.properCoproductTerms_left_order_lt hterm
      omega
    have hr : RootedForest.order term.2 ≤ m := by
      have := RootedForest.properCoproductTerms_right_order_lt hterm
      omega
    rw [hσ term.1 hl, hσ term.2 hr]
  have hcross : (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (adjointCharacter ψ).evalForest term.1 *
          ψ.evalForest term.2).sum =
      (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (adjointCharacter e).evalForest term.1 *
          e.evalForest term.2).sum := by
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    obtain ⟨htm, htp⟩ := List.mem_filter.1 hterm
    have htp' : 0 < RootedForest.order term.1 ∧
        0 < RootedForest.order term.2 := by simpa using htp
    have horder := RootedForest.coproductTerms_order htm
    have hl : RootedForest.order term.1 ≤ m := by omega
    have hr : RootedForest.order term.2 ≤ m := by omega
    rw [hadj term.1 hl, h term.2 hr]
  have hadj_def := Series.adjointCharacter_eval_first_defect h hτ
  rw [hm.neg_one_pow] at hadj_def
  rw [hproper_σ] at hτσ
  rw [hcross] at hτσ
  -- deduce that the square roots agree at τ
  have hAe : (adjointCharacter e).evalForest τ = e.evalForest τ := by
    rw [(isOdd_iff_adjointCharacter_eq e).1
      (Series.isOdd_toCharacter_exact (R := R))]
  have hσequal : RootedForest.sqrtCoeff
      (convolution (adjointCharacter ψ) ψ) τ =
      RootedForest.sqrtCoeff (convolution (adjointCharacter e) e) τ := by
    have h2 : (2 : R) ≠ 0 := two_ne_zero
    refine mul_left_cancel₀ h2 ?_
    linear_combination hτσ - hτσe + hadj_def - hAe
  -- expand the antisymmetric parts of ψ and of the exact character
  have hexpand : ∀ χ : Character R,
      antisymmetricPart χ (ofForest (R := R) τ) =
        ((RootedForest.coproductTerms τ).map fun term =>
          χ.evalForest term.1 * ((-1 : R) ^ RootedForest.order term.2 *
            RootedForest.sqrtCoeff
              (convolution (adjointCharacter χ) χ) term.2)).sum := by
    intro χ
    rw [antisymmetricPart, LinearFunctional.convolution_ofForest]
    refine congrArg List.sum (List.map_congr_left fun term _ => ?_)
    rw [LinearFunctional.compGradingInvolution_ofForest, symmetricPart,
      sqrtFunctional_ofForest]
    rfl
  have hψplus := hexpand ψ
  have heplus := hexpand e
  rw [RootedForest.sum_map_coproductTerms_split (R := R) hτne] at hψplus
  rw [RootedForest.sum_map_coproductTerms_split (R := R) hτne] at heplus
  -- the exact character has trivial antisymmetric part
  have hezero : antisymmetricPart e (ofForest (R := R) τ) = 0 := by
    rw [antisymmetricPart_of_isOdd (Series.isOdd_toCharacter_exact (R := R))]
    show ForestAlgebra.counit R (ofForest (R := R) τ) = 0
    rw [ForestAlgebra.counit_ofForest]
    simp [ForestAlgebra.counitCoeff, hτne]
  -- filtered cross terms agree
  have hfil : (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        ψ.evalForest term.1 * ((-1 : R) ^ RootedForest.order term.2 *
          RootedForest.sqrtCoeff
            (convolution (adjointCharacter ψ) ψ) term.2)).sum =
      (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        e.evalForest term.1 * ((-1 : R) ^ RootedForest.order term.2 *
          RootedForest.sqrtCoeff
            (convolution (adjointCharacter e) e) term.2)).sum := by
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    obtain ⟨htm, htp⟩ := List.mem_filter.1 hterm
    have htp' : 0 < RootedForest.order term.1 ∧
        0 < RootedForest.order term.2 := by simpa using htp
    have horder := RootedForest.coproductTerms_order htm
    have hl : RootedForest.order term.1 ≤ m := by omega
    have hr : RootedForest.order term.2 ≤ m := by omega
    rw [h term.1 hl, hσ term.2 hr]
  rw [hfil] at hψplus
  rw [hezero] at heplus
  rw [hσequal] at hψplus
  simp only [RootedForest.order_zero, pow_zero, one_mul,
    RootedForest.sqrtCoeff_zero, mul_one,
    Character.evalForest_zero] at hψplus heplus
  linear_combination hψplus - heplus

/-- A character is its own square root's square: `ψ = (ψ⋆ψ)^{1/2}`
pointwise. -/
theorem sqrtCoeff_convolution_self [Field R] [Invertible (2 : R)]
    (ψ : Character R) (φ : RootedForest) :
    RootedForest.sqrtCoeff (convolution ψ ψ) φ = ψ.evalForest φ := by
  have hone : LinearFunctional.ofCharacter ψ (ofForest (R := R) 0) = 1 := by
    show ψ (ofForest (R := R) 0) = 1
    rw [ofForest_zero]
    exact map_one ψ
  have hsq : LinearFunctional.convolution (LinearFunctional.ofCharacter ψ)
      (LinearFunctional.ofCharacter ψ) =
      LinearFunctional.ofCharacter (convolution ψ ψ) :=
    (linearFunctional_ofCharacter_convolution ψ ψ).symm
  have h := (sqrtFunctional_unique (convolution ψ ψ) hone hsq).symm
  have h2 := congrArg (fun f : LinearFunctional R =>
    f (ofForest (R := R) φ)) h
  simp only [sqrtFunctional_ofForest] at h2
  exact h2

/-- **Equivalence of the `SC` and `EC` order conditions**
(arXiv:2507.21006, Section 8): the antisymmetric order conditions
`ψ(τ⁺) = 0` up to order `m` hold iff the square-free conditions
`(ψ⋆ψ)(τ) = (ψ*⋆ψ)(τ)` hold up to order `m` — a criterion involving only
convolutions and the antipode, with no square roots. -/
theorem hasAntisymOrder_iff_convolution_agree [Field R] [CharZero R]
    [Invertible (2 : R)] (ψ : Character R) (m : ℕ) :
    HasAntisymOrder ψ m ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ m →
        (convolution ψ ψ).evalForest φ =
          (convolution (adjointCharacter ψ) ψ).evalForest φ := by
  have hσ_self : ∀ φ : RootedForest,
      LinearFunctional.evalForest (LinearFunctional.ofCharacter ψ) φ =
        LinearFunctional.evalForest (sqrtFunctional (convolution ψ ψ)) φ :=
    fun φ => by
      show LinearFunctional.ofCharacter ψ (ofForest (R := R) φ) =
        sqrtFunctional (convolution ψ ψ) (ofForest (R := R) φ)
      rw [sqrtFunctional_ofForest, sqrtCoeff_convolution_self]
      rfl
  constructor
  · -- antisymmetric order gives ψ ~ ψ⁻, hence the squares agree
    intro h φ hφ
    have hψσ : ∀ ρ : RootedForest, RootedForest.order ρ ≤ m →
        LinearFunctional.evalForest (LinearFunctional.ofCharacter ψ) ρ =
          LinearFunctional.evalForest (symmetricPart ψ) ρ := by
      intro ρ hρ
      have hdec := convolution_antisymmetricPart_symmetricPart ψ
      have hagree := LinearFunctional.AgreeUpToOrder.convolution
        (f := antisymmetricPart ψ) (f' := LinearFunctional.counit R)
        (g := symmetricPart ψ) (g' := symmetricPart ψ) (n := m)
        h (LinearFunctional.agreeUpToOrder_refl _ m) ρ hρ
      rw [hdec, LinearFunctional.convolution_counit_left] at hagree
      exact hagree
    have hsq := LinearFunctional.AgreeUpToOrder.convolution
      (f := LinearFunctional.ofCharacter ψ) (f' := symmetricPart ψ)
      (g := LinearFunctional.ofCharacter ψ) (g' := symmetricPart ψ)
      (n := m) hψσ hψσ φ hφ
    rw [convolution_symmetricPart] at hsq
    rw [show (convolution ψ ψ).evalForest φ =
      LinearFunctional.evalForest (LinearFunctional.ofCharacter
        (convolution ψ ψ)) φ from rfl,
      linearFunctional_ofCharacter_convolution]
    rw [show (convolution (adjointCharacter ψ) ψ).evalForest φ =
      LinearFunctional.evalForest (LinearFunctional.ofCharacter
        (convolution (adjointCharacter ψ) ψ)) φ from rfl]
    exact hsq
  · -- the squares agreeing forces ψ ~ ψ⁻, hence ψ⁺ ~ ε
    intro h
    have hconv : ∀ φ : RootedForest, RootedForest.order φ ≤ m →
        (convolution ψ ψ).evalForest φ =
          (convolution (adjointCharacter ψ) ψ).evalForest φ := h
    have hσagree := RootedForest.sqrtCoeff_congr m hconv
    have hψσ : ∀ ρ : RootedForest, RootedForest.order ρ ≤ m →
        LinearFunctional.evalForest (LinearFunctional.ofCharacter ψ) ρ =
          LinearFunctional.evalForest (symmetricPart ψ) ρ := by
      intro ρ hρ
      rw [hσ_self ρ]
      rw [LinearFunctional.evalForest, sqrtFunctional_ofForest,
        LinearFunctional.evalForest, symmetricPart, sqrtFunctional_ofForest]
      exact hσagree ρ hρ
    intro ρ hρ
    have hplus := LinearFunctional.AgreeUpToOrder.convolution
      (f := LinearFunctional.ofCharacter ψ) (f' := symmetricPart ψ)
      (g := LinearFunctional.compGradingInvolution (symmetricPart ψ))
      (g' := LinearFunctional.compGradingInvolution (symmetricPart ψ))
      (n := m) hψσ (LinearFunctional.agreeUpToOrder_refl _ m) ρ hρ
    rw [show LinearFunctional.convolution (symmetricPart ψ)
      (LinearFunctional.compGradingInvolution (symmetricPart ψ)) =
      LinearFunctional.counit R from
      convolution_symmetricPart_compGradingInvolution ψ] at hplus
    exact hplus

end

end Character

end ForestAlgebra

end BSeries
