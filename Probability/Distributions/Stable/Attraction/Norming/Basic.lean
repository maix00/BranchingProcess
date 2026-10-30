/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated.Basic
public import Analysis.Asymptotics.RegularVariation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Norming and scales in a stable domain of attraction

These deterministic quantities are defined from the one-step increment law `ν`.
Under attraction to a nondegenerate `α`-stable law, the normalized truncated
second moment is slowly varying; the definition alone does not assert that
property. The limiting stable law and the functional limit theorem remain
separate data.

## Public declarations

- `stableSlowVariation α ν u = u^(α - 2) ∫_{|x| ≤ u} x² ν(dx)` is the
  truncated-moment factor.
- `IsStableNorming α ν B` means `Bₙ > 0` for `n > 0`, `Bₙ → ∞`, and
  `Bₙ^α / (n L*ν(Bₙ)) → 1`.
- `stableSmallDeviationRate α ν a n = aₙ^α / (n L*ν(aₙ))`, and
  `stableRateNormalization α ν a n` is its reciprocal
  `n L*ν(aₙ) / aₙ^α`.
- `stableScaleTime α ν u = u^α / L*ν(u)`; for `α = 2`, this is
  `u² / ∫_{|x| ≤ u} x² ν(dx)`.
- The public identities express the `α = 2` specializations, positivity of
  `L*ν`, and `stableRateNormalization α ν a n = n / stableScaleTime α ν (aₙ)`.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

/-- The truncated-moment factor `L*` associated with the input increment law
`ν`. This definition makes no regularity assertion; proving slow variation
from stable-domain hypotheses is a separate theorem. For `0 < α < 2`, a
regularly varying two-sided tail is a sufficient condition. -/
noncomputable def stableSlowVariation
    (α : ℝ) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ (α - 2) * truncatedSecondMoment ν u

/-- A normalization satisfies the asymptotic inverse-norming condition for a
stable domain of attraction. The ratio tends to one rather than requiring an
exact identity. Positivity and divergence are recorded separately because
the asymptotic relation alone does not constrain finitely many initial terms. -/
def IsStableNorming (α : ℝ) (ν : Measure ℝ) (normalization : ℕ → ℝ) : Prop :=
  (∀ n, 0 < n → 0 < normalization n) ∧
    Tendsto normalization atTop atTop ∧
      Tendsto (fun n =>
        normalization n ^ α / stableSlowVariation α ν (normalization n) /
          (n : ℝ)) atTop (nhds 1)

/-- The logarithmic normalization in Mogulskii's `α`-stable
small-deviation theorem. -/
noncomputable def stableSmallDeviationRate
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  scale n ^ α / ((n : ℝ) * stableSlowVariation α ν (scale n))

@[simp] theorem stableSlowVariation_two (ν : Measure ℝ) (u : ℝ) :
    stableSlowVariation 2 ν u = truncatedSecondMoment ν u := by
  simp [stableSlowVariation]

@[simp] theorem stableSmallDeviationRate_two
    (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableSmallDeviationRate 2 ν scale n =
      scale n ^ 2 / ((n : ℝ) * truncatedSecondMoment ν (scale n)) := by
  simp [stableSmallDeviationRate]

/-- The rate normalization associated to a stable small-deviation scale. It is
the reciprocal of `stableSmallDeviationRate`; its value is
`n * L*ν (x n) / (x n)^α`. -/
noncomputable def stableRateNormalization
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  (stableSmallDeviationRate α ν scale n)⁻¹

/-- The rate normalization written out: `n * L* (x n) / x n ^ α`. -/
@[simp] theorem stableRateNormalization_eq
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α ν scale n =
      (n : ℝ) * stableSlowVariation α ν (scale n) / scale n ^ α := by
  rw [stableRateNormalization, stableSmallDeviationRate, inv_div]

/-- Mogulskii's slowly varying function is positive at a positive scale as soon
as the truncated second moment is. -/
theorem stableSlowVariation_pos {α : ℝ} {ν : Measure ℝ} {u : ℝ}
    (hu : 0 < u) (hmoment : 0 < truncatedSecondMoment ν u) :
    0 < stableSlowVariation α ν u :=
  mul_pos (Real.rpow_pos_of_pos hu _) hmoment

/-- A nonvanishing second moment makes the truncated second moment eventually
positive. -/
theorem eventually_truncatedSecondMoment_pos (ν : Measure ℝ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ u in atTop, 0 < truncatedSecondMoment ν u :=
  (tendsto_truncatedSecondMoment ν hν).eventually (isOpen_Ioi.mem_nhds hpos)

/-- Consequently `L*` is eventually positive. -/
theorem eventually_stableSlowVariation_pos (α : ℝ) (ν : Measure ℝ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ u in atTop, 0 < stableSlowVariation α ν u := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_truncatedSecondMoment_pos ν hν hpos] with u hu hmoment
  exact stableSlowVariation_pos hu hmoment

/-! ## The inverse norming function -/

/-- The characteristic step time at spatial scale `u` for increment law `ν`:
`κν(u) = u ^ α / L*ν(u)`. Under the corresponding regular-variation
hypotheses, this is asymptotically inverse to the stable normalization.

At `α = 2` it is `u ^ 2 / truncatedSecondMoment ν u`, the diffusive time scale. -/
noncomputable def stableScaleTime (α : ℝ) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ α / stableSlowVariation α ν u

@[simp] theorem stableScaleTime_two (ν : Measure ℝ) (u : ℝ) :
    stableScaleTime 2 ν u = u ^ 2 / truncatedSecondMoment ν u := by
  simp [stableScaleTime]

/-- The rate normalization is the number of steps divided by the scale time: `λ n = n / B* (x n)`,
the number of blocks of `B* (x n)` steps that fit into the `n` steps of the walk. -/
theorem stableRateNormalization_eq_natCast_div_stableScaleTime
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α ν scale n = (n : ℝ) / stableScaleTime α ν (scale n) := by
  simp only [stableRateNormalization_eq, stableScaleTime, div_eq_mul_inv]
  rw [mul_inv_rev, inv_inv]
  ring

end ProbabilityTheory
