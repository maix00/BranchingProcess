import Probability.Distributions.Stable.Attraction
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Normalization
import Probability.Asymptotics.BlockScale
import Probability.Asymptotics.Scale

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
open ProbabilityTheory.Asymptotics

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
    IsSmallDeviationScale scale normalization

namespace IsStableMogulskiiScale

theorem stableNorming
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    IsStableNorming α μ normalization := h.1

theorem scale_tendsto_atTop
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto scale atTop atTop := h.2.tendsto_atTop

theorem scale_div_normalization_tendsto_zero
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2.tendsto_div

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
    h.2.eventually_pos

/-- For a finite-variance stable normalization, the original two-scale condition
`scale n / normalization n → 0` makes the exponent-two small-deviation rate tend to zero.  This identifies
the block length as negligible relative to the full time horizon in the Gaussian specialization. -/
theorem tendsto_stableSmallDeviationRate_two_zero
    {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 μ normalization scale)
    (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvariance : 0 < ∫ x, x ^ 2 ∂μ) :
    Tendsto (stableSmallDeviationRate 2 μ scale) atTop (nhds 0) := by
  have hscaleMoment : Tendsto (fun n => stableSlowVariation 2 μ (scale n))
      atTop (nhds (∫ x, x ^ 2 ∂μ)) := by
    simpa only [Function.comp_def, stableSlowVariation_two] using
      (tendsto_truncatedSecondMoment μ hμ).comp hscale.scale_tendsto_atTop
  have hnormMoment : Tendsto (fun n => stableSlowVariation 2 μ (normalization n))
      atTop (nhds (∫ x, x ^ 2 ∂μ)) := by
    simpa only [Function.comp_def, stableSlowVariation_two] using
      (tendsto_truncatedSecondMoment μ hμ).comp hscale.stableNorming.2.1
  have hscaleMomentPos : ∀ᶠ n in atTop, 0 < stableSlowVariation 2 μ (scale n) :=
    (hscale.scale_tendsto_atTop).eventually
      (eventually_stableSlowVariation_pos 2 μ hμ hvariance)
  have hnormMomentPos : ∀ᶠ n in atTop, 0 < stableSlowVariation 2 μ (normalization n) :=
    hscale.stableNorming.2.1.eventually
      (eventually_stableSlowVariation_pos 2 μ hμ hvariance)
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratioSq : Tendsto (fun n => (scale n / normalization n) ^ 2)
      atTop (nhds 0) := by
    simpa only [pow_two, mul_zero] using hratio.mul hratio
  have hmomentRatio : Tendsto
      (fun n => stableSlowVariation 2 μ (normalization n) /
        stableSlowVariation 2 μ (scale n)) atTop (nhds 1) := by
    have h := hnormMoment.div hscaleMoment hvariance.ne'
    have hfun :
        (fun n => stableSlowVariation 2 μ (normalization n)) /
          (fun n => stableSlowVariation 2 μ (scale n)) =
        (fun n => stableSlowVariation 2 μ (normalization n) /
          stableSlowVariation 2 μ (scale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hvariance.ne'] using h
  have hproduct : Tendsto
      (fun n => (scale n / normalization n) ^ 2 *
        (stableSlowVariation 2 μ (normalization n) /
          stableSlowVariation 2 μ (scale n))) atTop (nhds 0) := by
    simpa using hratioSq.mul hmomentRatio
  have heq : stableSmallDeviationRate 2 μ scale =ᶠ[atTop]
      fun n => (scale n / normalization n) ^ 2 *
        (stableSlowVariation 2 μ (normalization n) /
          stableSlowVariation 2 μ (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscaleMomentPos, hnormMomentPos]
      with n hn hscalePos hnormPos
    rw [stableSmallDeviationRate_two]
    have hnormEquation :
        normalization n ^ (2 : ℝ) / truncatedSecondMoment μ (normalization n) = n := by
      simpa only [stableSlowVariation_two] using hscale.stableNorming.2.2 n hn
    rw [← hnormEquation]
    have hscaleMomentEq :
        stableSlowVariation 2 μ (scale n) = truncatedSecondMoment μ (scale n) :=
      stableSlowVariation_two μ (scale n)
    have hnormMomentEq :
        stableSlowVariation 2 μ (normalization n) =
          truncatedSecondMoment μ (normalization n) :=
      stableSlowVariation_two μ (normalization n)
    rw [hscaleMomentEq]
    rw [hnormMomentEq]
    have hnormValuePos : 0 < normalization n := hscale.stableNorming.1 n hn
    have hscaleTruncatedPos : 0 < truncatedSecondMoment μ (scale n) :=
      hscaleMomentEq ▸ hscalePos
    have hnormTruncatedPos : 0 < truncatedSecondMoment μ (normalization n) :=
      hnormMomentEq ▸ hnormPos
    field_simp [hscalePos.ne', hnormPos.ne', hscaleTruncatedPos.ne',
      hnormTruncatedPos.ne', hnormValuePos.ne']
    simp only [Real.rpow_two]
  exact hproduct.congr' heq.symm

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

/-- The unrounded number of steps in a stable small-deviation block. The spatial corridor scale is
`scale n`; by the inverse norming relation, a walk travels this distance in `B* (scale n) =
scale n ^ α / L* (scale n)` steps, up to the multiplicative block parameter `constant`. The separate stable
normalization `b n` is used to compare this block length with the full horizon `n`. -/
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
    Tendsto (stableBlockLength α μ constant scale) atTop atTop := by
  change Tendsto (floorBlockLength (stableBlockArgument α μ constant scale))
    atTop atTop
  exact tendsto_floorBlockLength_atTop
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- The block length is eventually positive along the block scale. -/
theorem eventually_stableBlockLength_pos
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α μ constant scale n := by
  change ∀ᶠ n in atTop,
    0 < floorBlockLength (stableBlockArgument α μ constant scale) n
  exact eventually_floorBlockLength_pos
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- Rounding the block length down does not change its ratio to the unrounded block length. -/
theorem tendsto_stableBlockArgument_floor_div
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K) :
    Tendsto (fun n => (⌊stableBlockArgument α μ constant scale n⌋₊ : ℝ) /
        stableBlockArgument α μ constant scale n) atTop (nhds 1) := by
  simpa [floorBlockLength] using
    (tendsto_floorBlockLength_div_argument
      (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation))

/-- The unrounded stable block length is `constant * n` times the small-deviation rate evaluated at the
corridor scale. -/
theorem stableBlockArgument_eq_mul_stableSmallDeviationRate
    {α : ℝ} {μ : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hn : (n : ℝ) ≠ 0) (hL : stableSlowVariation α μ (scale n) ≠ 0) :
    stableBlockArgument α μ constant scale n =
      constant * n * stableSmallDeviationRate α μ scale n := by
  have hden : (n : ℝ) * stableSlowVariation α μ (scale n) ≠ 0 := mul_ne_zero hn hL
  rw [stableBlockArgument, stableSmallDeviationRate]
  field_simp

/-- If the stable small-deviation rate tends to zero, one block occupies a vanishing fraction of the full
horizon. The hypotheses ensure the floor asymptotic and identify the unrounded block length with
`constant * n * stableSmallDeviationRate`. -/
theorem tendsto_stableBlockLength_div_nat_zero
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α μ scale) atTop (nhds 0)) :
    Tendsto (fun n => (stableBlockLength α μ constant scale n : ℝ) / n)
      atTop (nhds 0) := by
  have hfloor := tendsto_stableBlockArgument_floor_div hα hconstant hK hscale hvariation
  have hrateMul : Tendsto (fun n => constant * stableSmallDeviationRate α μ scale n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hargDiv : Tendsto (fun n => stableBlockArgument α μ constant scale n / n)
      atTop (nhds 0) := by
    have heq : (fun n => stableBlockArgument α μ constant scale n / n) =ᶠ[atTop]
        fun n => constant * stableSmallDeviationRate α μ scale n := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation] with n hn hvar
      rw [stableBlockArgument_eq_mul_stableSmallDeviationRate]
      · field_simp
      · exact_mod_cast hn.ne'
      · exact hvar.1.ne'
    exact hrateMul.congr' heq.symm
  have hmul : Tendsto
      (fun n => (⌊stableBlockArgument α μ constant scale n⌋₊ : ℝ) /
        stableBlockArgument α μ constant scale n *
          (stableBlockArgument α μ constant scale n / n))
      atTop (nhds 0) := by
    simpa using hfloor.mul hargDiv
  have heq : (fun n => (stableBlockLength α μ constant scale n : ℝ) / n) =ᶠ[atTop]
      fun n => (⌊stableBlockArgument α μ constant scale n⌋₊ : ℝ) /
        stableBlockArgument α μ constant scale n *
          (stableBlockArgument α μ constant scale n / n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation,
      hscale.eventually (eventually_gt_atTop 0)] with n hn hvar hscalePos
    have hargPos : 0 < stableBlockArgument α μ constant scale n := by
      rw [stableBlockArgument]
      exact div_pos (mul_pos hconstant (Real.rpow_pos_of_pos hscalePos α)) hvar.1
    simp only [stableBlockLength]
    field_simp [hargPos.ne', Nat.cast_ne_zero.mpr hn.ne']
  exact hmul.congr' heq.symm


end ProbabilityTheory.RandomWalk
