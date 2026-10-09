/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableRate
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Upper
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stable Mogulskii lower rate

The proof follows the source's endpoint-return construction. A large fixed
stable block is controlled by the stable endpoint-corridor rate, transferred
through the open-set Portmanteau inequality, and iterated by the discrete
seven-band return estimate. The block count is then evaluated using slow
variation alone.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- For every fixed strict interior tube, the stable endpoint-corridor
asymptotic and the stable block functional limit give an eventual exponential
lower bound for the strict horizontal-tube probability. The smaller closed
tube produced by the discrete return estimate is contained in the requested
open tube. -/
theorem eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {radius epsilon delta : ℝ}
    (hradius : 0 < radius) (hepsilon : 0 < epsilon)
    (hmargin : 4 * epsilon < radius)
    (hwidth : 2 * (radius + 4 * epsilon) < 1)
    (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / radius ^ α - delta) * c ^ α)) ^
            (n / stableBlockLength α ν (c ^ α) scale n + 1) ≤
          openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (scale n) n := by
  let rate : ℝ := C / radius ^ α
  have hscaledMass :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_scaledStableEndpointBandProbability_ge_exp
      hEscape hX hcdf hradius hepsilon hmargin (by linarith : 0 < delta / 2)
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1
    (hscaledMass.and (eventually_gt_atTop (0 : ℝ)))
  let c : ℝ := max c₀ 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcMass := hc₀ c (le_max_left _ _)
  have hcPower : 0 < c ^ α := Real.rpow_pos_of_pos hc α
  have hlowExponent :
      (rate - delta) * c ^ α < (rate - delta / 2) * c ^ α := by
    nlinarith
  have hlowENN : ENNReal.ofReal (Real.exp ((rate - delta) * c ^ α)) <
      ENNReal.ofReal (Real.exp ((rate - delta / 2) * c ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  let lowerBound : ENNReal := ENNReal.ofReal
    (Real.exp ((rate - delta) * c ^ α))
  have hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.scalePath c)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    intro i hi
    exact hlowENN.trans (hcMass.1 i hi)
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν (c ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow hcPower hscaleTop
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n :=
    hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hblockEq : blockLength = Asymptotics.floorBlockLength
      (fun n => c ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (c ^ α) scale n⌋₊ =
      ⌊c ^ α * stableScaleTime α ν (scale n)⌋₊
    rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
  have hnormRatioBase :=
    hscale.stableNorming.tendsto_floorBlock_normalization_div_scale
      hα hα₂ hslow hscaleTop hcPower
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (𝓝 c) := by
    have hbase : Tendsto
        (fun n => normalization (blockLength n) / scale n)
        atTop (𝓝 ((c ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [blockLength, hblockEq]
    have hroot : (c ^ α) ^ (1 / α) = c := by
      rw [← Real.rpow_mul (le_of_lt hc) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
        hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
        hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath c) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath c) hscaleMapMeas.aemeasurable (by simp)
  have hclosedLower :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit
      ν scale blockLength (fun n => n)
      (Z := Skorokhod.scalePath c) hlimit' hscalePos hblockPos
      hradius hepsilon lowerBound hbelow
  refine ⟨c, hc, ?_⟩
  filter_upwards [hclosedLower, hscalePos] with n hclosed hscaleN
  have hwidthAt :
      2 * (radius + 4 * epsilon) * scale n < scale n := by
    calc
      2 * (radius + 4 * epsilon) * scale n < 1 * scale n :=
        mul_lt_mul_of_pos_right hwidth hscaleN
      _ = scale n := by ring
  have hsubset :
      {increment | InHorizontalTube (1 / 2)
        (2 * (radius + 4 * epsilon) * scale n) n increment} ⊆
      {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} := by
    intro increment h
    change ∀ k : Fin n,
      -(1 / 2 : ℝ) * (2 * (radius + 4 * epsilon) * scale n) ≤
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * (radius + 4 * epsilon) * scale n) at h
    intro k
    rcases h k with ⟨hlo, hhi⟩
    constructor
    · exact (show -(1 / 2 : ℝ) * scale n <
        -(1 / 2 : ℝ) * (2 * (radius + 4 * epsilon) * scale n) by
          nlinarith).trans_le hlo
    · exact hhi.trans_lt (show
        (1 - (1 / 2 : ℝ)) * (2 * (radius + 4 * epsilon) * scale n) <
          (1 - (1 / 2 : ℝ)) * scale n by nlinarith)
  have hmono :
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * epsilon) * scale n) n ≤
      openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (scale n) n := by
    change iidSequenceLaw ν
        {increment | InHorizontalTube (1 / 2)
          (2 * (radius + 4 * epsilon) * scale n) n increment} ≤
      iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment}
    exact measure_mono hsubset
  exact hclosed.trans hmono

/-- The source endpoint-return construction gives the sharp stable lower
rate for every strict sub-tube. The radius may then approach the target
half-width; the block amplitude is fixed before taking the horizon limit. -/
theorem stableEscapeRate_subtube_liminf_lower
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {radius epsilon delta : ℝ}
    (hradius : 0 < radius) (hepsilon : 0 < epsilon)
    (hmargin : 4 * epsilon < radius)
    (hwidth : 2 * (radius + 4 * epsilon) < 1)
    (hdelta : 0 < delta) :
    C / radius ^ α - delta ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) := by
  let rate : ℝ := C / radius ^ α
  obtain ⟨c, hc, hprobLower⟩ :=
    eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      hradius hepsilon hmargin hwidth hdelta
  let constant : ℝ := c ^ α
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let blockCount : ℕ → ℕ := fun n => stableBlockCount α ν constant scale n
  let lowerReal : ℝ := Real.exp ((rate - delta) * constant)
  let lowerBound : ℝ≥0∞ := ENNReal.ofReal lowerReal
  let probability : ℕ → ℝ≥0∞ := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n
  let coefficient : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n * ((blockCount n + 1 : ℕ) : ℝ)
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact Real.rpow_pos_of_pos hc α
  have hlowerRealPos : 0 < lowerReal := by
    dsimp [lowerReal]
    exact Real.exp_pos _
  have hlowerBoundPos : 0 < lowerBound :=
    ENNReal.ofReal_pos.mpr hlowerRealPos
  have hblockCountRate :=
    tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
      hα hα₂ hconstant hscale hslow hrate
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hscalePos := IsStableMogulskiiScale.eventually_scale_pos hscale
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hslowPos]
      with n hn hs hL
    rw [stableSmallDeviationRate, stableScaleTime]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal, hL.ne']
  have hcountTerm : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n * (blockCount n : ℝ))
      atTop (𝓝 constant⁻¹) := by
    apply hblockCountRate.congr'
    filter_upwards [hrateEq] with n hn
    simp [blockCount, stableBlockCount, hn]
  have hcoefficient : Tendsto coefficient atTop (𝓝 constant⁻¹) := by
    have hsum := hcountTerm.add hrate
    have heq : coefficient =ᶠ[atTop]
        fun n => stableSmallDeviationRate α ν scale n *
          (blockCount n : ℝ) + stableSmallDeviationRate α ν scale n := by
      filter_upwards [] with n
      simp [coefficient]
      ring
    simpa [coefficient] using hsum.congr' heq.symm
  have hleft : Tendsto (fun n => coefficient n * Real.log lowerReal)
      atTop (𝓝 (constant⁻¹ * Real.log lowerReal)) :=
    hcoefficient.mul_const _
  have hleftValue : constant⁻¹ * Real.log lowerReal = rate - delta := by
    simp only [lowerReal, Real.log_exp]
    dsimp [constant]
    field_simp [ne_of_gt hconstant]
  rw [hleftValue] at hleft
  have hprobLower' : ∀ᶠ n in atTop,
      lowerBound ^ (n / blockLength n + 1) ≤ probability n := by
    filter_upwards [hprobLower] with n hn
    simpa [lowerBound, lowerReal, blockLength, blockCount,
      probability, stableBlockCount] using hn
  have hlog : ∀ᶠ n in atTop,
      coefficient n * Real.log lowerReal ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hprobLower', eventually_gt_atTop (0 : ℕ),
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos]
      with n hbound hn hs hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : lowerBound ^ (n / blockLength n + 1) ≠ ∞ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hreal : lowerReal ^ (n / blockLength n + 1) ≤
        (probability n).toReal := by
      have h := (ENNReal.toReal_le_toReal hpowTop hprobTop).2 hbound
      simpa [lowerBound, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hlowerRealPos.le] using h
    have hlogReal : ((n / blockLength n + 1 : ℕ) : ℝ) *
        Real.log lowerReal ≤ Real.log (probability n).toReal := by
      have h := Real.log_le_log
        (pow_pos hlowerRealPos _) hreal
      simpa [Real.log_pow] using h
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    calc
      coefficient n * Real.log lowerReal =
          stableSmallDeviationRate α ν scale n *
            ((n / blockLength n + 1 : ℕ) : ℝ) * Real.log lowerReal := by
        have hcountEq : blockCount n = n / blockLength n := by
          simp [blockCount, stableBlockCount, blockLength]
        simp [coefficient, hcountEq]
      _ ≤ stableSmallDeviationRate α ν scale n *
            Real.log (probability n).toReal := by
        nlinarith [mul_le_mul_of_nonneg_left hlogReal hrateNonneg]
  have hactualUpper : ∀ᶠ n in atTop,
      stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos]
      with n hn hs hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hprobRealOne : (probability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hlogNonpos := Real.log_nonpos ENNReal.toReal_nonneg hprobRealOne
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hrateNonneg hlogNonpos
  calc
    rate - delta = atTop.liminf (fun n => coefficient n * Real.log lowerReal) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n =>
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal) :=
      Filter.liminf_le_liminf hlog hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hactualUpper)

/-- Optimizing the strict interior radius up to one half removes the fixed
sub-tube loss and yields the sharp centered unit-width lower rate. -/
theorem stableEscapeRate_liminf_lower
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    C / ((1 / 2 : ℝ) ^ α) ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) := by
  let target : ℝ := C / ((1 / 2 : ℝ) ^ α)
  let marginSeq : ℕ → ℝ := fun k => 1 / ((k + 3 : ℕ) : ℝ)
  have hden : Tendsto (fun m : ℝ => (1 - m) / 2)
      (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    have hnum : Tendsto (fun m : ℝ => (1 : ℝ) - m)
        (𝓝 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub tendsto_id :
        Tendsto (fun m : ℝ => (1 : ℝ) - m)
          (𝓝 0) (𝓝 ((1 : ℝ) - 0)) )
    simpa using hnum.div_const (2 : ℝ)
  have hpow : Tendsto (fun m : ℝ => ((1 - m) / 2) ^ α)
      (𝓝 0) (𝓝 ((1 / 2 : ℝ) ^ α)) := by
    exact (Real.continuousAt_rpow_const (1 / 2 : ℝ) α
      (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hden
  have hdenPos : 0 < (1 / 2 : ℝ) ^ α :=
    Real.rpow_pos_of_pos (by norm_num) α
  have hrateMargin : Tendsto
      (fun m : ℝ => C / (((1 - m) / 2) ^ α))
      (𝓝 0) (𝓝 target) := by
    convert (tendsto_const_nhds.div hpow hdenPos.ne') using 1
  have hmarginSeqZero : Tendsto marginSeq atTop (𝓝 0) := by
    simpa [Function.comp_def, marginSeq, Nat.cast_add, div_eq_mul_inv] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 3)
  have hmarginSeqPos (k : ℕ) : 0 < marginSeq k := by
    dsimp [marginSeq]
    positivity
  have hmarginSeqLtHalf (k : ℕ) : marginSeq k < 1 / 2 := by
    have hk : 2 < k + 3 := by omega
    have hk' : (2 : ℝ) < ((k + 3 : ℕ) : ℝ) := by exact_mod_cast hk
    dsimp [marginSeq]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k + 3 : ℕ))]
    norm_num
    nlinarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hcloseTarget : target - δ / 2 < target := by linarith
  have hcloseEvent := (hrateMargin.comp hmarginSeqZero).eventually
    (Ioi_mem_nhds hcloseTarget)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcloseEvent
  let margin : ℝ := marginSeq N
  let radius : ℝ := (1 - margin) / 2
  let epsilon : ℝ := margin / 32
  have hmarginPos : 0 < margin := hmarginSeqPos N
  have hmarginSmall : margin < 1 / 2 := hmarginSeqLtHalf N
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hendpointMargin : 4 * epsilon < radius := by
    dsimp [epsilon, radius]
    nlinarith [hmarginPos, hmarginSmall]
  have hwidth : 2 * (radius + 4 * epsilon) < 1 := by
    dsimp [epsilon, radius]
    nlinarith [hmarginPos]
  have hclose : target - δ / 2 < C / radius ^ α := by
    simpa [target, radius, margin] using hN N le_rfl
  have hfixed := stableEscapeRate_subtube_liminf_lower
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
    hradius hepsilon hendpointMargin hwidth (by linarith : 0 < δ / 2)
  have htarget : target ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) + δ := by
    dsimp [target] at hclose ⊢
    linarith
  exact htarget

/-- The endpoint-return lower estimate supplies both eventual positivity and
the real-logarithm lower-coboundedness required by the upper Portmanteau
argument. The slowly varying factor is only assumed slowly varying; it need
not be bounded along the small-deviation scale. -/
theorem stableEscapeRate_eventually_positive_and_log_cobounded
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    (∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) ∧
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) := by
  have hfixed :=
    eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (0 : ℝ) < 1 / 64)
      (by norm_num : 4 * (1 / 64 : ℝ) < 1 / 3)
      (by norm_num : 2 * (1 / 3 + 4 * (1 / 64 : ℝ)) < 1)
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨c, hc, hprobLower⟩ := hfixed
  let radius : ℝ := 1 / 3
  let epsilon : ℝ := 1 / 64
  let delta : ℝ := 1
  let constant : ℝ := c ^ α
  let length : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let count : ℕ → ℕ := fun n => stableBlockCount α ν constant scale n
  let probability : ℕ → ℝ≥0∞ := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n
  let base : ℝ := Real.exp ((C / radius ^ α - delta) * constant)
  let baseENN : ℝ≥0∞ := ENNReal.ofReal base
  let coefficient : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n * ((count n + 1 : ℕ) : ℝ)
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact Real.rpow_pos_of_pos hc α
  have hbasePos : 0 < base := by
    dsimp [base]
    exact Real.exp_pos _
  have hbaseENNPos : 0 < baseENN := ENNReal.ofReal_pos.mpr hbasePos
  have hbaseENNPowPos : ∀ k : ℕ, 0 < baseENN ^ k := by
    intro k
    exact pos_iff_ne_zero.mpr (ENNReal.pow_ne_zero hbaseENNPos.ne' k)
  have hprobLower' : ∀ᶠ n in atTop,
      baseENN ^ (n / length n + 1) ≤ probability n := by
    filter_upwards [hprobLower] with n hn
    simpa [baseENN, base, radius, delta, length, count, probability,
      stableBlockCount] using hn
  have hpositive : ∀ᶠ n in atTop, 0 < probability n := by
    filter_upwards [hprobLower'] with n hn
    exact (hbaseENNPowPos _).trans_le hn
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hcountRate :=
    tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
      hα hα₂ hconstant hscale hslow hrate
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hscalePos := IsStableMogulskiiScale.eventually_scale_pos hscale
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hslowPos]
      with n hn hs hL
    rw [stableSmallDeviationRate, stableScaleTime]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal, hL.ne']
  have hcountTerm : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n * (count n : ℝ))
      atTop (𝓝 constant⁻¹) := by
    apply hcountRate.congr'
    filter_upwards [hrateEq] with n hn
    simp [count, stableBlockCount, hn]
  have hcoefficient : Tendsto coefficient atTop (𝓝 constant⁻¹) := by
    have hsum := hcountTerm.add hrate
    have heq : coefficient =ᶠ[atTop]
        fun n => stableSmallDeviationRate α ν scale n * (count n : ℝ) +
          stableSmallDeviationRate α ν scale n := by
      filter_upwards [] with n
      simp [coefficient]
      ring
    simpa [coefficient] using hsum.congr' heq.symm
  have hleft : Tendsto (fun n => coefficient n * Real.log base)
      atTop (𝓝 (constant⁻¹ * Real.log base)) := hcoefficient.mul_const _
  have hlog : ∀ᶠ n in atTop,
      coefficient n * Real.log base ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hprobLower', hpositive,
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      eventually_gt_atTop (0 : ℕ),
      hscaleTop.eventually hslow.eventually_pos]
      with n hbound hpos hs hn hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : baseENN ^ (n / length n + 1) ≠ ∞ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hreal : base ^ (n / length n + 1) ≤ (probability n).toReal := by
      have h := (ENNReal.toReal_le_toReal hpowTop hprobTop).2 hbound
      simpa [baseENN, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hbasePos.le] using h
    have hlogReal : ((n / length n + 1 : ℕ) : ℝ) * Real.log base ≤
        Real.log (probability n).toReal := by
      have h := Real.log_le_log (pow_pos hbasePos _) hreal
      simpa [Real.log_pow] using h
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    calc
      coefficient n * Real.log base =
          stableSmallDeviationRate α ν scale n *
            ((n / length n + 1 : ℕ) : ℝ) * Real.log base := by
        have hcountEq : count n = n / length n := by
          simp [count, stableBlockCount, length]
        simp [coefficient, hcountEq]
      _ ≤ stableSmallDeviationRate α ν scale n *
            Real.log (probability n).toReal := by
        nlinarith [mul_le_mul_of_nonneg_left hlogReal hrateNonneg]
  have hleftLower : ∀ᶠ n in atTop,
      constant⁻¹ * Real.log base - 1 < coefficient n * Real.log base :=
    hleft.eventually (Ioi_mem_nhds (by linarith :
      constant⁻¹ * Real.log base - 1 < constant⁻¹ * Real.log base))
  have hactualLower : ∀ᶠ n in atTop,
      constant⁻¹ * Real.log base - 1 ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hleftLower, hlog] with n hleftN hlogN
    exact hleftN.le.trans hlogN
  have hactualUpper : ∀ᶠ n in atTop,
      stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [IsStableMogulskiiScale.eventually_scale_pos hscale,
      eventually_gt_atTop (0 : ℕ),
      hscaleTop.eventually hslow.eventually_pos] with n hs hn hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hprobRealOne : (probability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hrateNonneg
      (Real.log_nonpos ENNReal.toReal_nonneg hprobRealOne)
  refine ⟨hpositive,
    Filter.isCoboundedUnder_le_of_eventually_le atTop hactualLower,
    ⟨constant⁻¹ * Real.log base - 1, hactualLower⟩,
    ⟨0, hactualUpper⟩⟩

/-- The two rate bounds identify the stable centered horizontal-tube limit.
The only scale assumption on `L*` is slow variation; no boundedness along
the shrinking-deviation scale is required. -/
theorem tendsto_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_of_escapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    Tendsto (fun n => stableSmallDeviationRate α ν scale n *
      Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) atTop
      (𝓝 (C / ((1 / 2 : ℝ) ^ α))) := by
  have hside := stableEscapeRate_eventually_positive_and_log_cobounded
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
  have hlower := stableEscapeRate_liminf_lower
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
  have hupper :=
    limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le
      hscale hα hα₂ hslow hEscape hDOA htightBase
      hside.1 hside.2.1
  exact tendsto_of_le_liminf_of_limsup_le hlower hupper
    hside.2.2.2 hside.2.2.1

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable
