/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Corridor energy

For real-valued corridor boundaries `lower` and `upper`, define the rate
functional

\[
  H_α(lower, upper) = \int_0^1 (upper(t) - lower(t))^{-α}\,dt.
\]

This is the finite-boundary energy in A. A. Mogul'skii, Theorem 1, equation
(15), “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081. The results record
constant-width, vertical-translation, widening, shrinking, and positive-scale
identities for this functional.

## Public declarations

* `corridorEnergy α lower upper` is the displayed integral defining
  `H_α(lower, upper)`.
* `corridorEnergy_const` states
  `H_α(c, d) = (d - c)^(-α)` for constant boundaries `c` and `d`.
* `corridorEnergy_add_const` states
  `H_α(lower + s, upper + s) = H_α(lower, upper)`.
* `corridorEnergy_add_sub` and `corridorEnergy_sub_add` give, respectively,
  `H_α(lower - ε, upper + ε) = ∫₀¹ (upper - lower + 2ε)^(-α)` and
  `H_α(lower + ε, upper - ε) = ∫₀¹ (upper - lower - 2ε)^(-α)`.
* `corridorEnergy_const_mul` states
  `H_α(a • lower, a • upper) = a^(-α) H_α(lower, upper)` when `a > 0` and
  `upper(t) - lower(t) > 0` for every `t`.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Rate

/-- The width functional `H_α` from Mogul'skii's Theorem 1: the integral over
the unit interval of the reciprocal `α`-power of the corridor width. -/
noncomputable def corridorEnergy (α : ℝ) (lower upper : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, (upper t - lower t) ^ (-α)

/-- A horizontal corridor of width `width` has energy `width⁻ᵅ`. -/
theorem corridorEnergy_const (α lower upper : ℝ) :
    corridorEnergy α (fun _ => lower) (fun _ => upper) =
      (upper - lower) ^ (-α) := by
  simp [corridorEnergy]

/-- Translating both boundaries leaves the corridor energy unchanged. -/
theorem corridorEnergy_add_const (α shift : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => shift + lower t)
        (fun t => shift + upper t) =
      corridorEnergy α lower upper := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-- Widening the boundaries by `ε` adds `2 * ε` to the width, so the energy of
the outer approximation is the integral of the reciprocal power of the widened
width. -/
theorem corridorEnergy_add_sub (α ε : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => lower t - ε) (fun t => upper t + ε) =
      ∫ t in Icc (0 : ℝ) 1, (upper t - lower t + 2 * ε) ^ (-α) := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-- Shrinking the boundaries by `ε` removes `2 * ε` from the width, so the
energy of the inner approximation is the integral of the reciprocal power of
the shrunk width. -/
theorem corridorEnergy_sub_add (α ε : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => lower t + ε) (fun t => upper t - ε) =
      ∫ t in Icc (0 : ℝ) 1, (upper t - lower t - 2 * ε) ^ (-α) := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-- Scaling both boundaries by `a > 0` scales the corridor energy by `a ^ (−α)`:
the energy of a corridor whose width is multiplied by `a` is the original energy
divided by `a ^ α`. -/
theorem corridorEnergy_const_mul {α a : ℝ} (ha : 0 < a) {lower upper : ℝ → ℝ}
    (hwidth : ∀ t, 0 < upper t - lower t) :
    corridorEnergy α (fun t => a * lower t) (fun t => a * upper t) =
      a ^ (-α) * corridorEnergy α lower upper := by
  rw [corridorEnergy, corridorEnergy, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hdiff : a * upper t - a * lower t = a * (upper t - lower t) := by ring
  rw [hdiff, Real.mul_rpow (le_of_lt ha) (le_of_lt (hwidth t))]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Rate
