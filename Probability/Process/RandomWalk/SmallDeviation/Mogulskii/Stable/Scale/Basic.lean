/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic

/-!
# Two-scale condition for stable small deviations

Write $a_n$ for the corridor scale and $b_n$ for the stable normalization.
## Public declarations

- `IsStableMogulskiiScale`: stable norming for $b_n$, together with
  $a_n\to\infty$ and $a_n/b_n\to0$.
- `IsStableMogulskiiScale.of_eventually_const_mul_normalization`,
  `IsStableMogulskiiScale.stableNorming`,
  `IsStableMogulskiiScale.scale_tendsto_atTop`,
  `IsStableMogulskiiScale.scale_div_normalization_tendsto_zero`,
  `IsStableMogulskiiScale.eventually_normalization_pos`,
  `IsStableMogulskiiScale.eventually_scale_pos`, and
  `IsStableMogulskiiScale.const_mul`: normalization and positive-rescaling
  rules for this two-scale condition.

This two-scale condition is the deterministic scale assumption in A. A.
Mogul'skii, *Small Deviations in a Space of Trajectories*, Theorem 3,
Section 4. Stable attraction and the one-block corridor estimate remain
separate hypotheses.

The source is A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory
open Asymptotics

/-! ## Stable scales -/

/-- The two-scale hypothesis used in the stable version of Mogulskii's
theorem.  `normalization` is the stable norming `bₙ`; `scale` is the smaller
corridor scale `aₙ`.  The stable law and the domain-of-attraction statement
are deliberately separate hypotheses and are not bundled into this
deterministic predicate.
-/
def IsStableMogulskiiScale
    (α : ℝ) (ν : Measure ℝ)
    (normalization scale : ℕ → ℝ) : Prop :=
  IsStableNorming α ν normalization ∧
    IsSmallDeviationScale scale normalization

namespace IsStableMogulskiiScale

/-- Replacing the raw domain-of-attraction normalization by an eventually
positive constant multiple preserves the two-scale hypothesis, provided the
replacement is already a stable norming for the same increment law. -/
theorem of_eventually_const_mul_normalization
    {α c : ℝ} {ν : Measure ℝ} {scale normalization normalization' : ℕ → ℝ}
    (hsmall : IsSmallDeviationScale scale normalization)
    (hnorm : IsStableNorming α ν normalization') (hc : 0 < c)
    (hnormalization_pos : ∀ᶠ n in atTop, 0 < normalization n)
    (hnormalization : normalization' =ᶠ[atTop]
      fun n => c * normalization n) :
    IsStableMogulskiiScale α ν normalization' scale :=
  ⟨hnorm, hsmall.of_eventually_const_mul hc hnormalization_pos hnormalization⟩

theorem stableNorming
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    IsStableNorming α ν normalization := h.1

theorem scale_tendsto_atTop
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    Tendsto scale atTop atTop := h.2.tendsto_atTop

theorem scale_div_normalization_tendsto_zero
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2.tendsto_div

theorem eventually_normalization_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < normalization n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact h.1.1 n hn

theorem eventually_scale_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
    h.2.eventually_pos

/-- A fixed positive multiple of a small-deviation scale is again a
small-deviation scale for the same stable norming. -/
theorem const_mul
    {α c : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) (hc : 0 < c) :
    IsStableMogulskiiScale α ν normalization (fun n => c * scale n) := by
  refine ⟨h.stableNorming,
    Asymptotics.IsSmallDeviationScale.of_tendsto ?_ ?_⟩
  · exact h.scale_tendsto_atTop.const_mul_atTop hc
  have hratio := h.scale_div_normalization_tendsto_zero.const_mul c
  simpa [div_eq_mul_inv, mul_assoc] using hratio

end IsStableMogulskiiScale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
