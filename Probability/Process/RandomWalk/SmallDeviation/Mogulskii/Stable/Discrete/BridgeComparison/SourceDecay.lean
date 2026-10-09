/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison.SourceAsymptotics
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison.CdfEntrance
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate

/-!
# Stable source endpoint decay

This module removes the finite-limit assumption on `L*` from the endpoint
decay step. Slow variation, the two-scale condition, and the stable norming
are sufficient: Potter bounds make the small-deviation rate vanish, so the
number of complete stable blocks tends to infinity.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The widened endpoint corridor probability tends to zero under the actual
stable-domain and two-scale hypotheses. No finite positive limit of the
slowly varying factor is assumed. -/
theorem tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain_slowVariation
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 0 < α) (hstable : IsStrictlyAlphaStable α μ)
    (hα₂ : α < 2)
    {normalization scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (ε c b : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0) := by
  classical
  have hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν) :=
    hDOA.isSlowlyVarying_stableSlowVariation hstable.isAlphaStable hα hα₂
  let C : ℝ := 2 * (1 + ε)
  let wideScale : ℕ → ℝ := fun n => C * scale n
  have hC : 0 < C := by dsimp [C]; positivity
  have hwideTop : Tendsto wideScale atTop atTop := by
    exact (hscale.scale_tendsto_atTop).const_mul_atTop hC
  have hwideDiv : Tendsto (fun n => wideScale n / normalization n)
      atTop (𝓝 0) := by
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul
      hscale.scale_div_normalization_tendsto_zero
    have heq : (fun n => C * (scale n / normalization n)) =ᶠ[atTop]
        fun n => wideScale n / normalization n := by
      filter_upwards [] with n
      dsimp [wideScale]
      ring
    simpa using hmul.congr' heq
  have hcenter : Tendsto
      (fun n : ℕ => (fun _ : ℕ => (0 : ℝ))
        (stableBlockLength α ν C wideScale n) / wideScale n)
      atTop (𝓝 0) := by
    simp
  obtain ⟨q, hq0, hq1, hupper⟩ :=
    eventually_horizontalTubeProbability_le_pow_of_strictStableDomain
      ν μ hstable hα₂ hC hnorm hwideTop hDOA hcenter
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  let block : ℕ → ℕ := stableBlockLength α ν C wideScale
  have hargumentEq (n : ℕ) : stableBlockArgument α ν C wideScale n =
      C * stableScaleTime α ν (wideScale n) := by
    rw [stableBlockArgument, stableScaleTime]
    ring
  have hblockEq : block = Asymptotics.floorBlockLength
      (fun n => C * stableScaleTime α ν (wideScale n)) := by
    funext n
    simp [block, stableBlockLength, Asymptotics.floorBlockLength, hargumentEq n]
  have hscaleTimeTop : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα
      (le_of_lt hα₂) hslow
  have hargumentTop : Tendsto
      (fun n => C * stableScaleTime α ν (wideScale n)) atTop atTop :=
    (hscaleTimeTop.comp hwideTop).const_mul_atTop hC
  have hblockTop : Tendsto block atTop atTop := by
    rw [hblockEq]
    exact Asymptotics.tendsto_floorBlockLength_atTop hargumentTop
  have hblockPos : ∀ᶠ n in atTop, 0 < block n := by
    simpa [block] using hblockTop.eventually (eventually_gt_atTop 0)
  have hrate : Tendsto (stableSmallDeviationRate α ν wideScale)
      atTop (𝓝 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hnorm hwideTop hwideDiv hα hα₂.le hslow
  have hwideSlowPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (wideScale n) :=
    hwideTop.eventually hslow.eventually_pos
  have hargumentDiv : Tendsto
      (fun n => stableBlockArgument α ν C wideScale n / (n : ℝ))
      atTop (𝓝 0) := by
    have hrateMul : Tendsto
        (fun n => C * stableSmallDeviationRate α ν wideScale n)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop
        (𝓝 C)).mul hrate
    have heq : (fun n => stableBlockArgument α ν C wideScale n / (n : ℝ)) =ᶠ[atTop]
        fun n => C * stableSmallDeviationRate α ν wideScale n := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hwideSlowPos] with n hn hL
      rw [stableBlockArgument_eq_mul_stableSmallDeviationRate]
      · field_simp
      · exact_mod_cast hn.ne'
      · exact hL.ne'
    exact hrateMul.congr' heq.symm
  have hfloorRatio : Tendsto
      (fun n => (block n : ℝ) /
        (C * stableScaleTime α ν (wideScale n))) atTop (𝓝 1) := by
    rw [hblockEq]
    exact Asymptotics.tendsto_floorBlockLength_div_argument hargumentTop
  have hblockDivZero : Tendsto (fun n => (block n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hprod : Tendsto
        (fun n => (block n : ℝ) /
          (C * stableScaleTime α ν (wideScale n)) *
          (stableBlockArgument α ν C wideScale n / (n : ℝ)))
        atTop (𝓝 0) := by
      simpa using hfloorRatio.mul hargumentDiv
    have heq : (fun n => (block n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (block n : ℝ) /
          (C * stableScaleTime α ν (wideScale n)) *
          (stableBlockArgument α ν C wideScale n / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ),
        hargumentTop.eventually (eventually_gt_atTop 0)] with n hn harg
      rw [hargumentEq n]
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hκPos : 0 < stableScaleTime α ν (wideScale n) := by
        by_contra hnot
        have hκle : stableScaleTime α ν (wideScale n) ≤ 0 := le_of_not_gt hnot
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos hC.le hκle
        linarith
      field_simp [hnNe, ne_of_gt hκPos]
    exact hprod.congr' heq.symm
  have hcount : Tendsto (fun n => n / block n) atTop atTop :=
    tendsto_nat_div_blockLength_atTop_of_blockLength_div_nat_zero
      block hblockPos hblockDivZero
  have hpow : Tendsto (fun n => q ^ (n / block n : ℕ)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hq0) hq1).comp hcount
  have htargetBound : ∀ᶠ n in atTop,
      (iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal ≤
        q ^ (n / block n : ℕ) := by
    filter_upwards [hupper] with n hupperN
    let wideTube : Set (ℕ → ℝ) :=
      {increment | InHorizontalTube (1 / 2) (wideScale n) n increment}
    have hsub : sourceEndpointCorridorEvent (scale n) ε c b n ⊆ wideTube := by
      intro increment hevent
      rcases hevent with ⟨htube, _⟩
      intro k
      have hk := htube k
      change -(1 / 2 : ℝ) * (2 * (1 + ε) * scale n) <
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment <
          (1 - (1 / 2 : ℝ)) * (2 * (1 + ε) * scale n) at hk
      change -(1 / 2 : ℝ) * wideScale n ≤
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * wideScale n
      rw [show wideScale n = 2 * (1 + ε) * scale n by
        dsimp [wideScale, C]]
      exact ⟨hk.1.le, hk.2.le⟩
    have hmeasure : iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n) ≤
        horizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (wideScale n) n := by
      change iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n) ≤ iidSequenceLaw ν wideTube
      exact measure_mono hsub
    have hmeasure' : iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n) ≤
          ENNReal.ofReal q ^ (n / block n) := hmeasure.trans hupperN
    have hleftTop : iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n) ≠ ⊤ := measure_ne_top _ _
    have hrightTop : ENNReal.ofReal q ^ (n / block n) ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmeasure'
    simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq0.le] using hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
  · exact Eventually.of_forall fun n => ENNReal.toReal_nonneg
  · exact htargetBound

/-- The source equation-(34) logarithmic comparison under the paper's stable
domain hypotheses, with no extra finite-limit assumption on `L*`. The bridge
comparison and base-corridor positivity are the existing source-specific
inputs; this theorem supplies the missing endpoint probability decay from
slow variation and the two-scale condition. -/
theorem exists_source_equation34_log_ratio_lower_of_stableDomain_slowVariation
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₂ : α < 2)
    (ε c b : ℝ) (hε : 0 < ε) (hc : -1 < c)
    (hcb : c < b) (hb : b < 1)
    (bridgeLength : ℕ → ℕ)
    (hscaleAll : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset SourceBridgeCenter, ∃ lowerBound : ℝ,
      F.Nonempty ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        1 - δ ≤ Real.log ((iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n)).toReal) /
          Real.log ((iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have hα : 0 < α := hP.strictlyStable.1
  have hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)) := by
    intro _ radius y hradius hylo hyhi x
    exact sourceBridgeEntrance_pos_of_cdfAtZero_allIndices hX hcdf
      radius x.1 y hradius x.2 ⟨hylo, hyhi⟩
  obtain ⟨F, lowerBound, hF, hlowerBound, hcomparison⟩ :=
    exists_source_equation34_finite_bridge_comparison_of_cdf
      hX hP hcdf ε c b hε hc hcb hb scale bridgeLength hscaleAll
      hbridgeLe hbridgePos hlow hlimit
  have hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n) :=
    eventually_sourceBaseCorridorEvent_pos_of_stableDomain
      hDOA hP hX hcdf htight hnorm hα hα₂ hscale.scale_tendsto_atTop
  have htargetZero : Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0) :=
    tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain_slowVariation
      ν μ hα hP.strictlyStable hα₂ hnorm hDOA hscale ε c b hε
  have hratio := eventually_one_sub_le_log_ratio_of_source_equation34
    F hF lowerBound hlowerBound ε c b scale hcomparison hbase htargetZero δ hδ
  exact ⟨F, lowerBound, hF, hlowerBound, hratio⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
