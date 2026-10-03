module

public import Probability.Distributions.Stable.Attraction
public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Asymptotics.BlockScale
public import Probability.Asymptotics.Scale

@[expose] public section

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
open scoped Topology

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
    (α : ℝ) (ν : Measure ℝ)
    (normalization scale : ℕ → ℝ) : Prop :=
  IsStableNorming α ν normalization ∧
    IsSmallDeviationScale scale normalization

namespace IsStableMogulskiiScale

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

/-- For a finite-variance stable normalization, the original two-scale condition
`scale n / normalization n → 0` makes the exponent-two small-deviation rate tend to zero.  This identifies
the block length as negligible relative to the full time horizon in the Gaussian specialization. -/
theorem tendsto_stableSmallDeviationRate_two_zero
    {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto (stableSmallDeviationRate 2 ν scale) atTop (nhds 0) := by
  have hscaleMoment : Tendsto (fun n => stableSlowVariation 2 ν (scale n))
      atTop (nhds (∫ x, x ^ 2 ∂ν)) := by
    simpa only [Function.comp_def, stableSlowVariation_two] using
      (tendsto_truncatedSecondMoment ν hν).comp hscale.scale_tendsto_atTop
  have hscaleMomentPos : ∀ᶠ n in atTop, 0 < stableSlowVariation 2 ν (scale n) :=
    (hscale.scale_tendsto_atTop).eventually
      (eventually_stableSlowVariation_pos 2 ν hν hvariance)
  have hnormValuePos := hscale.eventually_normalization_pos
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratioSq : Tendsto (fun n => (scale n / normalization n) ^ 2)
      atTop (nhds 0) := by
    simpa only [pow_two, mul_zero] using hratio.mul hratio
  have hnormSqDiv := IsStableNorming.tendsto_sq_div_nat hν hscale.stableNorming
  have hrateFactor : Tendsto
      (fun n => (normalization n ^ 2 / (n : ℝ)) /
        stableSlowVariation 2 ν (scale n)) atTop (nhds 1) := by
    have h := hnormSqDiv.div hscaleMoment hvariance.ne'
    have hfun : (fun n => normalization n ^ 2 / (n : ℝ)) /
        (fun n => stableSlowVariation 2 ν (scale n)) =
          (fun n => (normalization n ^ 2 / (n : ℝ)) /
            stableSlowVariation 2 ν (scale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hvariance.ne'] using h
  have hproduct : Tendsto
      (fun n => (scale n / normalization n) ^ 2 *
        ((normalization n ^ 2 / (n : ℝ)) /
          stableSlowVariation 2 ν (scale n))) atTop (nhds 0) := by
    simpa using hratioSq.mul hrateFactor
  have heq : stableSmallDeviationRate 2 ν scale =ᶠ[atTop]
      fun n => (scale n / normalization n) ^ 2 *
        ((normalization n ^ 2 / (n : ℝ)) /
          stableSlowVariation 2 ν (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscaleMomentPos,
      hnormValuePos] with n hn hscalePos hnormPos
    rw [stableSmallDeviationRate_two]
    rw [stableSlowVariation_two]
    have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnormNe : normalization n ≠ 0 := hnormPos.ne'
    have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := by
      have hpos : 0 < stableSlowVariation 2 ν (scale n) := hscalePos
      simpa only [stableSlowVariation_two] using hpos.ne'
    field_simp [hnpos, hnormNe, hmomentNe]
  exact hproduct.congr' heq.symm

/-- For any positive stability index, the two-scale condition makes the
small-deviation rate vanish once `L*` has a positive finite limit.  This is the
general-index scale estimate; unlike the preceding Gaussian result, it does
not use a finite second moment of the increment law. -/
theorem tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    {α ell : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hα : 0 < α) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) := by
  have hnormL : Tendsto
      (fun n => stableSlowVariation α ν (normalization n)) atTop (nhds ell) :=
    hslow.comp hscale.stableNorming.2.1
  have hscaleL : Tendsto
      (fun n => stableSlowVariation α ν (scale n)) atTop (nhds ell) :=
    hslow.comp hscale.scale_tendsto_atTop
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratioPow : Tendsto (fun n => (scale n / normalization n) ^ α)
      atTop (nhds 0) := hratio.rpow_const_nhds_zero hα
  have hnormFactor : Tendsto
      (fun n => normalization n ^ α /
        stableSlowVariation α ν (normalization n) / (n : ℝ))
      atTop (nhds 1) := hscale.stableNorming.2.2
  have hslowRatio : Tendsto
      (fun n => stableSlowVariation α ν (normalization n) /
        stableSlowVariation α ν (scale n)) atTop (nhds 1) := by
    have h := hnormL.div hscaleL hell.ne'
    have hfun : (fun n => stableSlowVariation α ν (normalization n)) /
        (fun n => stableSlowVariation α ν (scale n)) =
          (fun n => stableSlowVariation α ν (normalization n) /
            stableSlowVariation α ν (scale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hell.ne'] using h
  have hproduct : Tendsto
      (fun n => (scale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (scale n))) atTop (nhds 0) := by
    simpa using (hratioPow.mul hnormFactor).mul hslowRatio
  have hscalePos := hscale.eventually_scale_pos
  have hnormPos := hscale.eventually_normalization_pos
  have hnormLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (normalization n) := by
    filter_upwards [hnormL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have hscaleLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) := by
    filter_upwards [hscaleL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have heq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => (scale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hnormPos,
      hnormLPos, hscaleLPos] with n hn ha hb hLb hLa
    rw [stableSmallDeviationRate]
    rw [Real.div_rpow (le_of_lt ha) (le_of_lt hb) α]
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hbnNe : normalization n ≠ 0 := hb.ne'
    have haPowNe : scale n ^ α ≠ 0 := (Real.rpow_pos_of_pos ha α).ne'
    have hbPowNe : normalization n ^ α ≠ 0 := (Real.rpow_pos_of_pos hb α).ne'
    field_simp [hnNe, hbnNe, hLb.ne', hLa.ne', haPowNe, hbPowNe]
  exact hproduct.congr' heq.symm

/-- The corridor scale is eventually strictly below the norming. This is the only
consequence of `a n / b n → 0` that the block argument uses. -/
theorem eventually_scale_lt_normalization
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, scale n < normalization n := by
  have hlt : ∀ᶠ n in atTop, scale n / normalization n < 1 :=
    (tendsto_order.1 h.scale_div_normalization_tendsto_zero).2 1 zero_lt_one
  filter_upwards [h.eventually_normalization_pos, hlt] with n hn hlt
  exact (div_lt_one hn).mp hlt

/-- The two scale facts the block argument uses together. -/
theorem eventually_scale_pos_and_lt_normalization
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n ∧ scale n < normalization n :=
  h.eventually_scale_pos.and h.eventually_scale_lt_normalization

/-- `L*` is eventually positive along the corridor scale, so that the rate
`a n ^ α / (n * L* (a n))` has a nonvanishing denominator. -/
theorem eventually_slowVariation_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) :=
  h.scale_tendsto_atTop.eventually (eventually_stableSlowVariation_pos α ν hν hpos)

end IsStableMogulskiiScale

/-! ## Stable block lengths -/

/-- The unrounded number of steps in a stable small-deviation block. The spatial corridor scale is
`scale n`; by the inverse norming relation, a walk travels this distance in `B* (scale n) =
scale n ^ α / L* (scale n)` steps, up to the multiplicative block parameter `constant`. The separate stable
normalization `b n` is used to compare this block length with the full horizon `n`. -/
noncomputable def stableBlockArgument
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  constant * scale n ^ α / stableSlowVariation α ν (scale n)

/-- The number of steps of one block of the stable partition, the floor of `stableBlockArgument`. -/
noncomputable def stableBlockLength
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊stableBlockArgument α ν constant scale n⌋₊

/-- If the slowly varying factor of (3) stays in a positive interval along the block scale, then the
unrounded block length tends to infinity along it. -/
theorem tendsto_stableBlockArgument_atTop
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (stableBlockArgument α ν constant scale) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have hlow : ∀ᶠ n in atTop, b ≤ (constant / K) * scale n ^ α :=
    ((tendsto_rpow_atTop hα).comp hscale |>.const_mul_atTop (div_pos hconstant hK)).eventually
      (eventually_ge_atTop b)
  filter_upwards [hlow, hvariation, hscale.eventually (eventually_gt_atTop 0)] with n hb hn hsn
  have hpow : 0 < scale n ^ α := Real.rpow_pos_of_pos hsn _
  have hstep : (constant / K) * scale n ^ α ≤
      constant * scale n ^ α / stableSlowVariation α ν (scale n) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hconstant hpow)) hn.1 hn.2
  rw [stableBlockArgument]
  linarith

/-- The block length tends to infinity along the block scale. -/
theorem tendsto_stableBlockLength_atTop
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (stableBlockLength α ν constant scale) atTop atTop := by
  change Tendsto (floorBlockLength (stableBlockArgument α ν constant scale))
    atTop atTop
  exact tendsto_floorBlockLength_atTop
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- The block length is eventually positive along the block scale. -/
theorem eventually_stableBlockLength_pos
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α ν constant scale n := by
  change ∀ᶠ n in atTop,
    0 < floorBlockLength (stableBlockArgument α ν constant scale) n
  exact eventually_floorBlockLength_pos
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- Rounding the block length down does not change its ratio to the unrounded block length. -/
theorem tendsto_stableBlockArgument_floor_div
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n) atTop (nhds 1) := by
  simpa [floorBlockLength] using
    (tendsto_floorBlockLength_div_argument
      (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation))

/-- The rounded stable block length is asymptotic to the stable time scale
times its fixed block parameter.  This is the rounding relation for
`mₙ = ⌊constant · B*(aₙ)⌋₊`; it does not yet identify the norming at `mₙ` with
`aₙ`, which requires regular variation of the inverse norming. -/
theorem tendsto_stableBlockLength_div_stableScaleTime
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) atTop (nhds constant) := by
  have hfloor := tendsto_stableBlockArgument_floor_div
    hα hconstant hK hscale hvariation
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hvariation]
      with n hscalePos hvar
    exact div_pos (Real.rpow_pos_of_pos hscalePos α) hvar.1
  have hargRatio : Tendsto
      (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) atTop (nhds constant) := by
    have hargEq (n : ℕ) : stableBlockArgument α ν constant scale n =
        constant * stableScaleTime α ν (scale n) := by
      rw [stableBlockArgument, stableScaleTime]
      ring
    have heq : (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) =ᶠ[atTop] fun _ => constant := by
      filter_upwards [hscaleTimePos] with n htime
      rw [hargEq n]
      field_simp [htime.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hmul : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
        (stableBlockArgument α ν constant scale n /
          stableScaleTime α ν (scale n))) atTop (nhds (1 * constant)) := by
    simpa [stableBlockLength, floorBlockLength] using hfloor.mul hargRatio
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) =ᶠ[atTop]
      fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
        (stableBlockArgument α ν constant scale n /
          stableScaleTime α ν (scale n)) := by
    filter_upwards [hscaleTimePos,
      eventually_stableBlockLength_pos hα hconstant hK hscale hvariation]
      with n htime hlen
    have hargEq : stableBlockArgument α ν constant scale n =
        constant * stableScaleTime α ν (scale n) := by
      rw [stableBlockArgument, stableScaleTime]
      ring
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [hargEq]
      exact mul_pos hconstant htime
    field_simp [htime.ne', hargPos.ne']
  simpa using hmul.congr' heq.symm

/-- If the slowly varying factor has a positive finite limit, the norming at a
rounded stable block length has the expected spatial scale.  This is the
normalization bridge needed by the domain-of-attraction block endpoint
theorem.  The hypothesis on the limit is kept explicit here; proving it for
the stable limit law is a separate distributional tail theorem. -/
theorem tendsto_stableBlockNorming_div_scale_of_slowVariation_limit
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {constant ell : ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hell : 0 < ell)
    (hscale : Tendsto scale atTop atTop)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell))
    (hnorm : IsStableNorming α ν normalization) :
    Tendsto (fun n => normalization (stableBlockLength α ν constant scale n) /
      scale n) atTop (nhds (constant ^ (1 / α))) := by
  let block : ℕ → ℕ := stableBlockLength α ν constant scale
  have hslowWindow : ∀ᶠ u in atTop,
      0 < stableSlowVariation α ν u ∧ stableSlowVariation α ν u ≤ ell + 1 := by
    have hmem : Set.Ioo (ell / 2) (ell + 1) ∈ 𝓝 ell := by
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [hslow.eventually hmem]
      with u hu
    exact ⟨by linarith, by linarith⟩
  have hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧
        stableSlowVariation α ν (scale n) ≤ ell + 1 :=
    hscale.eventually hslowWindow
  have hblockTop : Tendsto block atTop atTop := by
    simpa [block] using tendsto_stableBlockLength_atTop
      hα hconstant (by linarith : 0 < ell + 1) hscale hvariation
  have hblockScale : Tendsto
      (fun n => (block n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds constant) := by
    simpa [block] using tendsto_stableBlockLength_div_stableScaleTime
      hα hconstant (by linarith : 0 < ell + 1) hscale hvariation
  have hslowScale : Tendsto (fun n => stableSlowVariation α ν (scale n))
      atTop (nhds ell) := hslow.comp hscale
  have hslowBlock : Tendsto
      (fun n => stableSlowVariation α ν (normalization (block n)))
      atTop (nhds ell) := by
    exact hslow.comp (hnorm.2.1.comp hblockTop)
  have hnormRatioBlock : Tendsto
      (fun n => normalization (block n) ^ α /
        stableSlowVariation α ν (normalization (block n)) / (block n : ℝ))
      atTop (nhds 1) := hnorm.2.2.comp hblockTop
  have hnormPowerBlock : Tendsto
      (fun n => normalization (block n) ^ α / (block n : ℝ))
      atTop (nhds ell) := by
    have hmul := hnormRatioBlock.mul hslowBlock
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (normalization (block n)) := by
      filter_upwards [hslowBlock.eventually (Ioi_mem_nhds hell)] with n hn
      exact hn
    have heq : (fun n => normalization (block n) ^ α /
        stableSlowVariation α ν (normalization (block n)) / (block n : ℝ) *
          stableSlowVariation α ν (normalization (block n))) =ᶠ[atTop]
        fun n => normalization (block n) ^ α / (block n : ℝ) := by
      filter_upwards [hblockPos, hslowPos] with n hn hL
      field_simp [show (block n : ℝ) ≠ 0 by exact_mod_cast hn.ne', hL.ne']
    simpa only [one_mul] using hmul.congr' heq
  have hblockOverScalePow : Tendsto
      (fun n => (block n : ℝ) / scale n ^ α) atTop
      (nhds (constant / ell)) := by
    have hdiv := hblockScale.div hslowScale hell.ne'
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    have hslowPos : ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) := by
      filter_upwards [hslowScale.eventually (Ioi_mem_nhds hell)] with n hn
      exact hn
    have heq : (fun n => (block n : ℝ) / stableScaleTime α ν (scale n) /
        stableSlowVariation α ν (scale n)) =ᶠ[atTop]
        fun n => (block n : ℝ) / scale n ^ α := by
      filter_upwards [hscalePos, hslowPos] with n hx hL
      rw [stableScaleTime]
      field_simp [hL.ne', (Real.rpow_pos_of_pos hx α).ne']
    exact hdiv.congr' heq
  have hratioPower : Tendsto
      (fun n => (normalization (block n) / scale n) ^ α) atTop
        (nhds constant) := by
    have hmul := hnormPowerBlock.mul hblockOverScalePow
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    have hnormPos : ∀ᶠ n in atTop, 0 < normalization (block n) := by
      filter_upwards [hblockPos] with n hn
      exact hnorm.1 (block n) hn
    have heq : (fun n => normalization (block n) ^ α / (block n : ℝ) *
        ((block n : ℝ) / scale n ^ α)) =ᶠ[atTop]
        fun n => (normalization (block n) / scale n) ^ α := by
      filter_upwards [hblockPos, hscalePos, hnormPos] with n hm hx hb
      rw [Real.div_rpow (le_of_lt hb) (le_of_lt hx)]
      have hmne : (block n : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hxpowne : scale n ^ α ≠ 0 := (Real.rpow_pos_of_pos hx α).ne'
      field_simp [hmne, hxpowne]
    have hlim : ell * (constant / ell) = constant := by
      field_simp [hell.ne']
    simpa only [hlim] using hmul.congr' heq
  have hroot : Tendsto
      (fun n => ((normalization (block n) / scale n) ^ α) ^ (1 / α))
      atTop (nhds (constant ^ (1 / α))) :=
    hratioPower.rpow_const (Or.inl hconstant.ne')
  have hratioPos : ∀ᶠ n in atTop,
      0 < normalization (block n) / scale n := by
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    filter_upwards [hblockPos, hscalePos] with n hm hx
    exact div_pos (hnorm.1 (block n) hm) hx
  have heq : (fun n => ((normalization (block n) / scale n) ^ α) ^ (1 / α)) =ᶠ[atTop]
      fun n => normalization (block n) / scale n := by
    filter_upwards [hratioPos] with n hn
    rw [← Real.rpow_mul (le_of_lt hn) α (1 / α)]
    rw [show α * (1 / α) = 1 by field_simp]
    exact Real.rpow_one _
  simpa using hroot.congr' heq

/-- The unrounded stable block length is `constant * n` times the small-deviation rate evaluated at the
corridor scale. -/
theorem stableBlockArgument_eq_mul_stableSmallDeviationRate
    {α : ℝ} {ν : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hn : (n : ℝ) ≠ 0) (hL : stableSlowVariation α ν (scale n) ≠ 0) :
    stableBlockArgument α ν constant scale n =
      constant * n * stableSmallDeviationRate α ν scale n := by
  have hden : (n : ℝ) * stableSlowVariation α ν (scale n) ≠ 0 := mul_ne_zero hn hL
  rw [stableBlockArgument, stableSmallDeviationRate]
  field_simp

/-- If the stable small-deviation rate tends to zero, one block occupies a vanishing fraction of the full
horizon. The hypotheses ensure the floor asymptotic and identify the unrounded block length with
`constant * n * stableSmallDeviationRate`. -/
theorem tendsto_stableBlockLength_div_nat_zero
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) / n)
      atTop (nhds 0) := by
  have hfloor := tendsto_stableBlockArgument_floor_div hα hconstant hK hscale hvariation
  have hrateMul : Tendsto (fun n => constant * stableSmallDeviationRate α ν scale n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hargDiv : Tendsto (fun n => stableBlockArgument α ν constant scale n / n)
      atTop (nhds 0) := by
    have heq : (fun n => stableBlockArgument α ν constant scale n / n) =ᶠ[atTop]
        fun n => constant * stableSmallDeviationRate α ν scale n := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation] with n hn hvar
      rw [stableBlockArgument_eq_mul_stableSmallDeviationRate]
      · field_simp
      · exact_mod_cast hn.ne'
      · exact hvar.1.ne'
    exact hrateMul.congr' heq.symm
  have hmul : Tendsto
      (fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / n))
      atTop (nhds 0) := by
    simpa using hfloor.mul hargDiv
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) / n) =ᶠ[atTop]
      fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation,
      hscale.eventually (eventually_gt_atTop 0)] with n hn hvar hscalePos
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [stableBlockArgument]
      exact div_pos (mul_pos hconstant (Real.rpow_pos_of_pos hscalePos α)) hvar.1
    simp only [stableBlockLength]
    field_simp [hargPos.ne', Nat.cast_ne_zero.mpr hn.ne']
  exact hmul.congr' heq.symm


end ProbabilityTheory.RandomWalk
