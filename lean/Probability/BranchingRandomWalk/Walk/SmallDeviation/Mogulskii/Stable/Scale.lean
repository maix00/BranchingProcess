import Probability.Distributions.Stable.Attraction
import Probability.Distributions.Stable.SmallDeviation

/-!
# Scales for the stable Mogulskii route

This file records the deterministic scale interface used by Mogulskii's
stable-domain-of-attraction proof.  The finite-variance files use
`IsMogulskiiScale`, which is based on the diffusive scale `sqrt n`.  The
stable proof has two visible scales instead: a stable normalization `b n` and
a smaller corridor scale `a n`.

The stable law, the domain-of-attraction statement, and the one-block
corridor estimate remain separate hypotheses.  This module only contains
the scale predicate and its elementary rounding lemmas.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory

/-! ## Stable scales -/

/-- The two-scale hypothesis used in the stable version of Mogulskii's
theorem.  `normalization` is the stable norming `bₙ`; `scale` is the smaller
corridor scale `aₙ`.  The stable law and the domain-of-attraction statement
are deliberately separate hypotheses and are not bundled into this
deterministic predicate.
-/
def IsStableMogulskiiScale
    (α : ℝ) (μ : Measure ℝ)
    (normalization scale : ℕ → ℝ) : Prop :=
  IsStableNorming α μ normalization ∧
    Tendsto scale atTop atTop ∧
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0)

namespace IsStableMogulskiiScale

theorem stableNorming
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    IsStableNorming α μ normalization := h.1

theorem scale_tendsto_atTop
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto scale atTop atTop := h.2.1

theorem scale_div_normalization_tendsto_zero
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2.2

theorem eventually_normalization_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < normalization n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact h.1.1 n hn

theorem eventually_scale_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
  h.2.1.eventually (eventually_gt_atTop 0)

/-- The corridor scale is eventually strictly below the norming. This is the only
consequence of `a n / b n → 0` that the block argument uses. -/
theorem eventually_scale_lt_normalization
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, scale n < normalization n := by
  have hlt : ∀ᶠ n in atTop, scale n / normalization n < 1 :=
    (tendsto_order.1 h.scale_div_normalization_tendsto_zero).2 1 zero_lt_one
  filter_upwards [h.eventually_normalization_pos, hlt] with n hn hlt
  exact (div_lt_one hn).mp hlt

/-- The two scale facts the block argument uses together. -/
theorem eventually_scale_pos_and_lt_normalization
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n ∧ scale n < normalization n :=
  h.eventually_scale_pos.and h.eventually_scale_lt_normalization

/-- `L*` is eventually positive along the corridor scale, so that the rate
`a n ^ α / (n * L* (a n))` has a nonvanishing denominator. -/
theorem eventually_slowVariation_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale)
    (hμ : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < ∫ x, x ^ 2 ∂μ) :
    ∀ᶠ n in atTop, 0 < stableSlowVariation α μ (scale n) :=
  h.scale_tendsto_atTop.eventually (eventually_stableSlowVariation_pos α μ hμ hpos)

end IsStableMogulskiiScale

/-! ## Stable block lengths -/

/-- The unrounded number of steps of one block of the stable partition: the stretch of the walk over
which the normalized path advances by the small-deviation scale `scale n`. A stretch of `t` steps
advances the walk by `B t`, and `B* = u ^ α / L* u` is inverse to `B` by (4) of the original paper, so
the stretch that advances by `scale n` is `scale n ^ α / L* (scale n)` steps, up to the constant factor
`constant`. -/
noncomputable def stableBlockArgument
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  constant * scale n ^ α / stableSlowVariation α μ (scale n)

/-- The number of steps of one block of the stable partition, the floor of `stableBlockArgument`. -/
noncomputable def stableBlockLength
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊stableBlockArgument α μ constant scale n⌋₊

/-- If the slowly varying factor of (3) stays in a positive interval along the block scale, then the
unrounded block length tends to infinity along it. -/
theorem tendsto_stableBlockArgument_atTop
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    Tendsto (stableBlockArgument α μ constant scale) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have hlow : ∀ᶠ n in atTop, b ≤ (constant / K) * scale n ^ α :=
    ((tendsto_rpow_atTop hα).comp hscale |>.const_mul_atTop (div_pos hconstant hK)).eventually
      (eventually_ge_atTop b)
  filter_upwards [hlow, hvariation, hscale.eventually (eventually_gt_atTop 0)] with n hb hn hsn
  have hpow : 0 < scale n ^ α := Real.rpow_pos_of_pos hsn _
  have hstep : (constant / K) * scale n ^ α ≤
      constant * scale n ^ α / stableSlowVariation α μ (scale n) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hconstant hpow)) hn.1 hn.2
  rw [stableBlockArgument]
  linarith

/-- The block length tends to infinity along the block scale. -/
theorem tendsto_stableBlockLength_atTop
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    Tendsto (stableBlockLength α μ constant scale) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- The block length is eventually positive along the block scale. -/
theorem eventually_stableBlockLength_pos
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α μ constant scale n :=
  (tendsto_stableBlockLength_atTop hα hconstant hK hscale hvariation).eventually
    (eventually_gt_atTop 0)

/-- Rounding the block length down does not change its ratio to the unrounded block length. -/
theorem tendsto_stableBlockArgument_floor_div
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    Tendsto (fun n => (⌊stableBlockArgument α μ constant scale n⌋₊ : ℝ) /
        stableBlockArgument α μ constant scale n) atTop (nhds 1) :=
  (tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

end ProbabilityTheory.RandomWalk
