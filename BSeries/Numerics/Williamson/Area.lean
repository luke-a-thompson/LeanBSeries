/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Area closure of the Williamson coefficient path

Lemma 1 of `papers/williamson_order_transfer.tex`. Natural indices allow any
finite prefix of the coefficient list, including lists containing zeros.
`segmentArea` is the polynomial antiderivative of `X_u dX_v - X_v dX_u`
on a straight segment. The conclusion includes interior segment points,
which is essential when taking areas of areas.
-/

namespace BSeries.RungeKutta.WilliamsonPath

variable {R : Type*} [CommRing R]

/-- The increment register, after `n` evaluations. -/
def register (α u : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => α n * register α u n + u n

/-- The coefficient path at the stage boundaries. -/
def endpoint (α β u : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => endpoint α β u n + β n * register α u (n + 1)

/-- The column `(Au) ⊙ v - (Av) ⊙ u`, with `A` given by the prefixes. -/
def bracket (α β u v : ℕ → R) (n : ℕ) : R :=
  endpoint α β u n * v n - endpoint α β v n * u n

/-- The alternating row identity in the proof of Lemma 1. -/
theorem register_bracket (α β u v : ℕ → R) (n : ℕ) :
    register α (bracket α β u v) (n + 1) =
      endpoint α β u n * register α v (n + 1) -
        endpoint α β v n * register α u (n + 1) := by
  induction n with
  | zero => simp [register, bracket, endpoint]
  | succ n ih =>
      simp only [register, bracket, endpoint] at ih ⊢
      linear_combination α (n + 1) * ih

/-- The linearly interpolated coefficient path on segment `n`. -/
def segment (α β u : ℕ → R) (n : ℕ) (θ : R) : R :=
  endpoint α β u n + θ * (β n * register α u (n + 1))

/-- Accumulated signed area at stage boundaries. On a straight segment
the quadratic terms cancel, so its area increment is this determinant. -/
def areaEndpoint (α β u v : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => areaEndpoint α β u v n +
      endpoint α β u n * (β n * register α v (n + 1)) -
      endpoint α β v n * (β n * register α u (n + 1))

/-- Polynomial signed area up to any point of segment `n`. -/
def segmentArea (α β u v : ℕ → R) (n : ℕ) (θ : R) : R :=
  areaEndpoint α β u v n + θ *
    (endpoint α β u n * (β n * register α v (n + 1)) -
      endpoint α β v n * (β n * register α u (n + 1)))

/-- Equality of the area integrands throughout each segment. -/
theorem area_integrand (α β u v : ℕ → R) (n : ℕ) (θ : R) :
    segment α β u n θ * (β n * register α v (n + 1)) -
      segment α β v n θ * (β n * register α u (n + 1)) =
        β n * register α (bracket α β u v) (n + 1) := by
  rw [register_bracket]
  unfold segment
  ring

theorem areaEndpoint_eq (α β u v : ℕ → R) (n : ℕ) :
    areaEndpoint α β u v n = endpoint α β (bracket α β u v) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [areaEndpoint, endpoint, ih, register_bracket]
      ring

/-- **Closure under areas**, including between stage points (Lemma 1).
No division, nonvanishing, positivity, or distinct-node assumption is used. -/
theorem area_eq (α β u v : ℕ → R) (n : ℕ) (θ : R) :
    segmentArea α β u v n θ = segment α β (bracket α β u v) n θ := by
  unfold segmentArea segment
  rw [areaEndpoint_eq, register_bracket]
  ring

end BSeries.RungeKutta.WilliamsonPath
