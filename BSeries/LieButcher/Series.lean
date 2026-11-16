/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.MKWDual

/-!
# Lie–Butcher series

Following Munthe-Kaas–Wright (arXiv:math/0603023, Section 2), a Lie series
on a manifold is a formal sum `LS(α) = Σ_{ω ∈ OF} h^{|ω|} α(ω) F(ω)` over
ordered forests, determined by its coefficient family `α`. We work at the
coefficient level: an `LSSeries` is a function on ordered (planar) forests.

Two classes are distinguished by their behaviour under the shuffle product:

* **exponential (group-like)** series, the shuffle characters — these
  represent flows of Lie group integrators and form a group under the
  Grossman–Larson convolution (`PlanarForest.mkwConvolution`);
* **logarithmic (algebra-like)** series, which represent vector fields;
  by Ree's criterion these are the functionals vanishing on the empty
  forest and on all shuffle products of non-empty forests. A logarithmic
  series is the non-commutative generalization of a B-series, called a
  **Lie–Butcher series**.

As verification we check the paper's example: the commutator
`τ₁τ₂ - τ₂τ₁` of two trees is logarithmic, as is any single tree.
-/

namespace BSeries

open HopfAlgebras


universe u

/-- The coefficient family of a Lie series on a manifold: one coefficient
per ordered forest (arXiv:math/0603023, eq. (2.4)). -/
abbrev LSSeries (R : Type u) : Type u :=
  PlanarForest → R

namespace LSSeries

variable {R : Type u}

/-- An LS-series is **exponential** (group-like) if its coefficients form a
shuffle character; these represent flows, and Lie group integrators are
exactly the exponential series (arXiv:math/0603023, Section 2). -/
def IsExponential [Semiring R] (α : LSSeries R) : Prop :=
  PlanarForest.IsShuffleCharacter α

/-- An LS-series is **logarithmic** (algebra-like), i.e. a
**Lie–Butcher series**, if it vanishes on the empty forest and on all
shuffle products of non-empty forests (Ree's shuffle criterion for lying
in the free Lie algebra; arXiv:math/0603023, Section 2). -/
def IsLieButcher [Semiring R] (α : LSSeries R) : Prop :=
  α [] = 0 ∧ ∀ ω₁ ω₂ : PlanarForest, ω₁ ≠ [] → ω₂ ≠ [] →
    ((Word.shuffle ω₁ ω₂).map α).sum = 0

/-- Composition of LS-series: the Grossman–Larson convolution dual to the
MKW coproduct (arXiv:math/0603023, Section 3). -/
def compose [Semiring R] (α β : LSSeries R) : LSSeries R :=
  PlanarForest.mkwConvolution α β

/-- The composition of exponential series is exponential: Lie group
integrators are closed under composition. -/
theorem IsExponential.compose [CommSemiring R] {α β : LSSeries R}
    (hα : IsExponential α) (hβ : IsExponential β) :
    IsExponential (α.compose β) :=
  PlanarForest.IsShuffleCharacter.mkwConvolution hα hβ

/-- The single-tree series `δ_τ`. -/
def singleTree [Zero R] [One R] [DecidableEq PlanarForest]
    (τ : PlanarTree) : LSSeries R :=
  fun ω => if ω = [τ] then 1 else 0

/-- The commutator series `τ₁τ₂ - τ₂τ₁` of two trees
(arXiv:math/0603023, Section 2). -/
def commutator [AddGroup R] [One R] [DecidableEq PlanarForest]
    (τ₁ τ₂ : PlanarTree) : LSSeries R :=
  fun ω => (if ω = [τ₁, τ₂] then (1 : R) else 0) -
    (if ω = [τ₂, τ₁] then (1 : R) else 0)

/-- The **symmetric defect** of an LB character: the Grossman–Larson
composition of the grading-signed character with the character itself —
the LB character of the roundtrip `Φ_{-h} ∘ Φ_h`
(arXiv:2509.20599, Theorem E.1(2)). -/
def symmetricDefect [Ring R] (φ : LSSeries R) : LSSeries R :=
  PlanarForest.mkwConvolution
    (fun ω => (-1 : R) ^ PTree.orderList ω * φ ω) φ

/-- An LB character has **antisymmetric order** `m` if its symmetric
defect vanishes on every planar tree of order at most `m`: the roundtrip
`Φ_{-h} ∘ Φ_h` recovers the identity to order `m`. -/
def HasPlanarAntisymOrder [Ring R] (φ : LSSeries R) (m : ℕ) : Prop :=
  ∀ τ : PTree, PTree.order τ ≤ m → symmetricDefect φ [τ] = 0

section Verification

variable [DecidableEq PlanarForest]

omit [DecidableEq PlanarForest] in
private theorem length_of_mem_shuffle {ω₁ ω₂ σ : PlanarForest}
    (h : σ ∈ Word.shuffle ω₁ ω₂) :
    σ.length = ω₁.length + ω₂.length := by
  have hperm := Word.perm_append_of_mem_shuffle h
  rw [hperm.length_eq, List.length_append]

/-- **A single tree is a Lie–Butcher series**: any shuffle of non-empty
forests has at least two trees. -/
theorem isLieButcher_singleTree [Semiring R] (τ : PlanarTree) :
    IsLieButcher (singleTree (R := R) τ) := by
  constructor
  · simp [singleTree]
  · intro ω₁ ω₂ h₁ h₂
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    have hlen := length_of_mem_shuffle hσ
    have h₁' : 0 < ω₁.length := List.length_pos_iff.2 h₁
    have h₂' : 0 < ω₂.length := List.length_pos_iff.2 h₂
    have hne : σ ≠ [τ] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    simp [singleTree, hne]

/-- **The commutator of two trees is a Lie–Butcher series**
(arXiv:math/0603023, Section 2): `τ₁τ₂ - τ₂τ₁` represents the commutator
of two vector fields, and its shuffle sums cancel in pairs. -/
theorem isLieButcher_commutator [Ring R] (τ₁ τ₂ : PlanarTree) :
    IsLieButcher (commutator (R := R) τ₁ τ₂) := by
  constructor
  · simp [commutator]
  · intro ω₁ ω₂ h₁ h₂
    by_cases hlen2 : ω₁.length + ω₂.length = 2
    · -- both forests are single trees; the two shuffles cancel
      have h₁' : 0 < ω₁.length := List.length_pos_iff.2 h₁
      have h₂' : 0 < ω₂.length := List.length_pos_iff.2 h₂
      have hl₁ : ω₁.length = 1 := by omega
      have hl₂ : ω₂.length = 1 := by omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl₁
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hl₂
      have hshuffle : Word.shuffle [a] [b] = [[a, b], [b, a]] := by
        simp
      rw [hshuffle]
      simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, commutator]
      -- the two shuffles hit the two monomials symmetrically
      have e1 : (([a, b] : PlanarForest) = [τ₁, τ₂]) ↔
          (([b, a] : PlanarForest) = [τ₂, τ₁]) := by
        constructor <;> (intro h; simp_all)
      have e2 : (([a, b] : PlanarForest) = [τ₂, τ₁]) ↔
          (([b, a] : PlanarForest) = [τ₁, τ₂]) := by
        constructor <;> (intro h; simp_all)
      by_cases hc1 : ([a, b] : PlanarForest) = [τ₁, τ₂]
      · have hc4 := e1.1 hc1
        by_cases hc2 : ([a, b] : PlanarForest) = [τ₂, τ₁]
        · have hc3 := e2.1 hc2
          rw [if_pos hc1, if_pos hc2, if_pos hc3, if_pos hc4]
          simp
        · have hc3 : ¬([b, a] : PlanarForest) = [τ₁, τ₂] :=
            fun h => hc2 (e2.2 h)
          rw [if_pos hc1, if_neg hc2, if_neg hc3, if_pos hc4]
          simp
      · have hc4 : ¬([b, a] : PlanarForest) = [τ₂, τ₁] :=
          fun h => hc1 (e1.2 h)
        by_cases hc2 : ([a, b] : PlanarForest) = [τ₂, τ₁]
        · have hc3 := e2.1 hc2
          rw [if_neg hc1, if_pos hc2, if_pos hc3, if_neg hc4]
          simp
        · have hc3 : ¬([b, a] : PlanarForest) = [τ₁, τ₂] :=
            fun h => hc2 (e2.2 h)
          rw [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4]
          simp
    · -- shuffles have the wrong length to meet either monomial
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
      have hlen := length_of_mem_shuffle hσ
      have hne1 : σ ≠ [τ₁, τ₂] := by
        intro h
        rw [h] at hlen
        simp at hlen
        omega
      have hne2 : σ ≠ [τ₂, τ₁] := by
        intro h
        rw [h] at hlen
        simp at hlen
        omega
      simp [commutator, hne1, hne2]

section ExactFlow

variable [DecidableEq PlanarTree]

/-- **The exact flow as a Lie series** (arXiv:math/0603023, Section 2):
the `t = 1` flow of a vector field `f = F(•)` pulls back functions by the
operator exponential `Exp(f) = Σ_j f^j / j!`, a Lie series supported on
the concatenation powers `• ⋯ •` of the single-node tree with
coefficients `1/j!`. -/
def exactFlow (R : Type u) [DivisionRing R] : LSSeries R :=
  fun ω => if ∀ t ∈ ω, t = PTree.bullet
    then ((Nat.factorial ω.length : R))⁻¹ else 0

omit [DecidableEq PlanarForest] in
/-- **The exact flow is exponential (group-like)**
(arXiv:math/0603023, Section 2): its coefficients form a shuffle
character, by the binomial identity `C(a+b,a)/(a+b)! = 1/a! ⋅ 1/b!`. -/
theorem isExponential_exactFlow (R : Type u) [Field R] [CharZero R] :
    IsExponential (exactFlow R) := by
  constructor
  · rw [exactFlow]
    simp
  · intro ω₁ ω₂
    by_cases h₁ : ∀ t ∈ ω₁, t = PTree.bullet
    · by_cases h₂ : ∀ t ∈ ω₂, t = PTree.bullet
      · -- both all-bullet: every shuffle is the same power of the bullet
        have hconst : ∀ σ ∈ Word.shuffle ω₁ ω₂, exactFlow R σ =
            ((Nat.factorial (ω₁.length + ω₂.length) : R))⁻¹ := by
          intro σ hσ
          have hmem : ∀ t ∈ σ, t = PTree.bullet := by
            intro t ht
            have hsub := (Word.perm_append_of_mem_shuffle hσ).subset ht
            rcases List.mem_append.1 hsub with h | h
            · exact h₁ t h
            · exact h₂ t h
          rw [exactFlow]
          rw [if_pos hmem, length_of_mem_shuffle hσ]
        rw [List.map_congr_left hconst, List.map_const', List.sum_replicate,
          Word.length_shuffle, nsmul_eq_mul, exactFlow, exactFlow,
          if_pos h₁, if_pos h₂]
        have hc := Nat.choose_mul_factorial_mul_factorial
          (Nat.le_add_right ω₁.length ω₂.length)
        rw [Nat.add_sub_cancel_left] at hc
        have hcast : (((ω₁.length + ω₂.length).choose ω₁.length : ℕ) : R) *
            (Nat.factorial ω₁.length : R) *
            (Nat.factorial ω₂.length : R) =
            (Nat.factorial (ω₁.length + ω₂.length) : R) := by
          exact_mod_cast congrArg (fun k : ℕ => (k : R)) hc
        have hfa : (Nat.factorial ω₁.length : R) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        have hfb : (Nat.factorial ω₂.length : R) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        have hfab : (Nat.factorial (ω₁.length + ω₂.length) : R) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        field_simp
        linear_combination hcast
      · -- a non-bullet tree of ω₂ lies in every shuffle
        rw [show exactFlow R ω₂ = 0 from if_neg h₂, mul_zero]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
        push Not at h₂
        obtain ⟨t₀, ht₀, hne⟩ := h₂
        have hσne : ¬ ∀ t ∈ σ, t = PTree.bullet := by
          intro hall
          refine hne (hall t₀ ?_)
          exact (Word.perm_append_of_mem_shuffle hσ).mem_iff.2
            (List.mem_append.2 (Or.inr ht₀))
        exact if_neg hσne
    · -- a non-bullet tree of ω₁ lies in every shuffle
      rw [show exactFlow R ω₁ = 0 from if_neg h₁, zero_mul]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
      push Not at h₁
      obtain ⟨t₀, ht₀, hne⟩ := h₁
      have hσne : ¬ ∀ t ∈ σ, t = PTree.bullet := by
        intro hall
        refine hne (hall t₀ ?_)
        exact (Word.perm_append_of_mem_shuffle hσ).mem_iff.2
          (List.mem_append.2 (Or.inl ht₀))
      exact if_neg hσne

end ExactFlow

end Verification

end LSSeries

end BSeries
