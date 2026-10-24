import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.OrderOfElement

/-!
# Polynomial rotation and the primitive spectral root

The coefficient recurrence gives a rotation identity. Propagating a root through a half turn and using coprimality locates it in the spectral orbit. Separability and root counting then determine the orbit and its full period.
-/

namespace Polynomial

noncomputable section
variable {R : Type*} [Field R]

theorem polynomial_rotation (p : R[X]) (q a : R)
    (hrec : ∀ k, p.coeff (k + 1) * (q ^ (k + 1) - 1) =
      a * p.coeff k * (q ^ k + 1)) :
    (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p := by
  ext n
  cases n with
  | zero => simp
  | succ k =>
      simp only [sub_mul, add_mul, one_mul, coeff_sub, coeff_add, mul_assoc,
        coeff_C_mul, coeff_X_mul, comp_C_mul_X_coeff]
      linear_combination hrec k

/-- A root must reach the vanishing rotation prefactor before its negative is reached. -/
theorem root_orbit_of_rotation (p : R[X]) (q a : R) {s : ℕ}
    (hc : IsCoprime p (p.comp (-X))) (hqs : q ^ s = -1)
    (hrot : (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p)
    {x : R} (hx : p.eval x = 0) : ∃ j < s, x = (a * q ^ j)⁻¹ := by
  by_contra! h
  have hprop (k : ℕ) (hk : k ≤ s) : p.eval (q ^ k * x) = 0 := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have he := congrArg (eval (q ^ k * x)) hrot
      simp only [eval_mul, eval_sub, eval_one, eval_comp, eval_C, eval_X, eval_add,
        ih (by omega), mul_zero] at he
      have hn : 1 - a * (q ^ k * x) ≠ 0 := by
        intro hz
        have hz' : a * q ^ k * x = 1 := by linear_combination -hz
        exact h k (by omega) (eq_inv_of_mul_eq_one_right hz')
      simpa [pow_succ', mul_assoc] using (mul_eq_zero.mp he).resolve_left hn
  have hn := (aeval_ne_zero_of_isCoprime hc x).resolve_left (by simpa using hx)
  exact hn (by simpa [hqs] using hprop s le_rfl)

/-- Counting the distinct roots determines the spectral orbit and its full period. -/
theorem roots_order_of_rotation (p : R[X]) (q a : R) {s : ℕ}
    (hs : 0 < s) (hp : p ≠ 0) (hdeg : p.natDegree = s) (hsplit : p.Splits)
    (hsep : (p * p.comp (-X)).Separable) (hqs : q ^ s = -1)
    (hrot : (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p) :
    orderOf q = 2 * s ∧ ∀ j < s, p.eval ((a * q ^ j)⁻¹) = 0 := by
  classical
  let f : ℕ → R := fun j => (a * q ^ j)⁻¹
  have hcard : p.roots.toFinset.card = s := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.of_mul_left),
      ← hsplit.natDegree_eq_card_roots, hdeg]
  have hsub : p.roots.toFinset ⊆ (Finset.range s).image f := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := root_orbit_of_rotation p q a hsep.isCoprime hqs hrot
      ((mem_roots hp).mp (Multiset.mem_toFinset.mp hx))
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [hcard] using (Finset.card_image_le (s := Finset.range s) (f := f)))
  have hinj : Set.InjOn f (Finset.range s) := Finset.card_image_iff.mp (by
    rw [← heq, hcard, Finset.card_range])
  have hroot (j : ℕ) (hj : j < s) : p.eval (f j) = 0 := by
    apply (mem_roots hp).mp
    rw [← Multiset.mem_toFinset, heq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  refine ⟨?_, hroot⟩
  have hpow : q ^ (2 * s) = 1 := by rw [mul_comm 2 s, pow_mul, hqs]; simp
  have hpos : 0 < orderOf q :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * s, by omega, hpow⟩).orderOf_pos
  have hle := orderOf_le_of_pow_eq_one (by omega : 0 < 2 * s) hpow
  by_contra hne
  by_cases hd : orderOf q < s
  · have := hinj (Finset.mem_range.mpr hd) (Finset.mem_range.mpr hs)
      (show f (orderOf q) = f 0 by simp [f])
    omega
  · have hk : orderOf q - s < s := by omega
    have hneg : q ^ (orderOf q - s) = -1 := by
      have h := pow_orderOf_eq_one q
      rw [← Nat.sub_add_cancel (by omega : s ≤ orderOf q), pow_add, hqs] at h
      linear_combination -h
    have hx := hroot (orderOf q - s) hk
    have hn := (aeval_ne_zero_of_isCoprime hsep.isCoprime (f 0)).resolve_left
      (by simpa using hroot 0 hs)
    apply hn
    simpa [f, hneg] using hx

end
end Polynomial
