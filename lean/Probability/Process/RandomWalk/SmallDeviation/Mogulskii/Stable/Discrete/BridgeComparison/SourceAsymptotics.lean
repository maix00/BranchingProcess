/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceLower
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.UpperEndpointSource
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

/-! # Source equation (34) asymptotics

This module proves base-corridor positivity, endpoint-corridor decay, and the
logarithmic-ratio consequence of the source finite bridge comparison. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- If the block length is negligible compared with the horizon, the source
quotient block count tends to infinity. -/
theorem tendsto_nat_div_blockLength_atTop_of_blockLength_div_nat_zero
    (blockLength : ℕ → ℕ)
    (hpos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hzero : Tendsto (fun n => (blockLength n : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => n / blockLength n) atTop atTop := by
  have hratioPos : ∀ᶠ n in atTop,
      0 < (blockLength n : ℝ) / (n : ℝ) := by
    filter_upwards [hpos, eventually_gt_atTop 0] with n hblock hn
    exact div_pos (Nat.cast_pos.mpr hblock) (Nat.cast_pos.mpr hn)
  have hratioWithin : Tendsto
      (fun n => (blockLength n : ℝ) / (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hratioPos⟩
  have hinv : Tendsto
      (fun n => ((blockLength n : ℝ) / (n : ℝ))⁻¹) atTop atTop :=
    hratioWithin.inv_tendsto_nhdsGT_zero
  have heq : (fun n => ((blockLength n : ℝ) / (n : ℝ))⁻¹) =ᶠ[atTop]
      fun n => (n : ℝ) / (blockLength n : ℝ) := by
    filter_upwards [hpos, eventually_gt_atTop 0] with n hblock hn
    have hblockNe : (blockLength n : ℝ) ≠ 0 := by
      exact_mod_cast hblock.ne'
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hblockNe, hnNe]
  have hinv' : Tendsto (fun n : ℕ => (n : ℝ) / (blockLength n : ℝ)) atTop atTop :=
    hinv.congr' heq
  apply Filter.tendsto_atTop.2
  intro N
  have hlarge := hinv'.eventually_ge_atTop (N : ℝ)
  filter_upwards [hlarge, hpos] with n hn hblock
  apply (Nat.le_div_iff_mul_le hblock).2
  have hmul : (N : ℝ) * (blockLength n : ℝ) ≤ (n : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hblock)).1 hn
  exact_mod_cast hmul

/-- The source lower endpoint-band estimate makes the original open unit
corridor event positive.  The lower estimate controls a closed tube whose
radius is strictly smaller than the unit radius, hence it is contained in the
open source event. -/
theorem eventually_sourceBaseCorridorEvent_pos_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hα₂ : α < 2)
    (hscale : Tendsto scale atTop atTop) :
    ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) (horizon n)) := by
  obtain ⟨r, lowerBound, hr, hrhalf, hlower, htube⟩ :=
    eventually_horizontalTubeProbability_ge_pow_of_stableDomain
      hDOA hP hX hcdf htight hnorm hα hα₂ hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hrSmall : r + 4 * (r / 16) < 1 := by nlinarith
  filter_upwards [htube, hscalePos] with n hbound hscaleN
  let narrowRadius : ℝ := r + 4 * (r / 16)
  have hradPos : 0 < narrowRadius := by
    dsimp [narrowRadius]
    positivity
  have hradLt : narrowRadius < 1 := by
    simpa [narrowRadius] using hrSmall
  have hwidthLt : 2 * narrowRadius * scale n < 2 * scale n :=
    mul_lt_mul_of_pos_right (by nlinarith [hradLt]) (hscaleN)
  have hclosedSubset :
      {increment : ℕ → ℝ |
        InHorizontalTube (1 / 2) (2 * narrowRadius * scale n)
          (horizon n) increment} ⊆
        sourceBaseCorridorEvent (scale n) (horizon n) := by
    intro increment htubeN
    change InOpenHorizontalTube (1 / 2 : ℝ) (2 * scale n)
      (horizon n) increment
    intro k
    have hk := htubeN k
    change -(1 / 2 : ℝ) * (2 * narrowRadius * scale n) ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        (1 - (1 / 2 : ℝ)) * (2 * narrowRadius * scale n) at hk
    constructor <;> nlinarith [hwidthLt, hk.1, hk.2]
  have hmeasure :
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
          (2 * narrowRadius * scale n) (horizon n) ≤
        iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) (horizon n)) := by
    change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          InHorizontalTube (1 / 2) (2 * narrowRadius * scale n)
            (horizon n) increment} ≤ _
    exact measure_mono hclosedSubset
  have hpow : 0 < lowerBound ^
      (horizon n / stableBlockLength α ν 1 scale n + 1) :=
    ENNReal.pow_pos hlower _
  exact hpow.trans_le (hbound.trans hmeasure)

/-- The finite-cell comparison transfers positivity of the base corridor to
positivity of the source endpoint corridor. -/
theorem eventually_sourceEndpointCorridorEvent_pos_of_equation34
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Finset SourceBridgeCenter) (lowerBound : ℝ)
    (hlowerBound : 0 < lowerBound)
    (ε c b : ℝ) (scale : ℕ → ℝ)
    (hcomparison : ∀ᶠ n in atTop,
      ENNReal.ofReal lowerBound * iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n) ≤
      (F.card : ℝ≥0∞) * iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n))
    (hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)) :
    ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal := by
  have hbaseToReal : ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal := by
    filter_upwards [hbase] with n hn
    exact ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  filter_upwards [hcomparison, hbase, hbaseToReal] with n hcomp hbaseN hbaseReal
  let μbase := iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)
  let μtarget := iidSequenceLaw ν
    (sourceEndpointCorridorEvent (scale n) ε c b n)
  have hleft : 0 < ENNReal.ofReal lowerBound * μbase :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hlowerBound).ne' hbaseN.ne'
  have htarget : 0 < μtarget := by
    by_contra hnot
    have hzero : μtarget = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have hcomp' : ENNReal.ofReal lowerBound * μbase ≤ 0 := by
      simpa [μbase, μtarget, hzero] using hcomp
    exact (not_lt_of_ge hcomp') hleft
  exact ENNReal.toReal_pos htarget.ne' (measure_ne_top _ _)

/-- Once the source equation (34) comparison is known, base-corridor
positivity and endpoint-corridor decay give the logarithmic-ratio bound. -/
theorem eventually_one_sub_le_log_ratio_of_source_equation34
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Finset SourceBridgeCenter) (hF : F.Nonempty)
    (lowerBound : ℝ) (hlowerBound : 0 < lowerBound)
    (ε c b : ℝ) (scale : ℕ → ℝ)
    (hcomparison : ∀ᶠ n in atTop,
      ENNReal.ofReal lowerBound * iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n) ≤
      (F.card : ℝ≥0∞) * iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n))
    (hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n))
    (htargetZero : Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      1 - δ ≤ Real.log ((iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n)).toReal) /
        Real.log ((iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have htarget := eventually_sourceEndpointCorridorEvent_pos_of_equation34
    F lowerBound hlowerBound ε c b scale hcomparison hbase
  have hbaseReal : ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal := by
    filter_upwards [hbase] with n hn
    exact ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  exact Asymptotics.eventually_one_sub_le_log_ratio_of_mul_bound
    ((F.card : ℝ) / lowerBound)
    (div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hF)) hlowerBound)
    (by
      filter_upwards [hcomparison] with n hn
      have hleftTop : ENNReal.ofReal lowerBound * iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
      have hrightTop : (F.card : ℝ≥0∞) * iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
      have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hn
      have hreal' : lowerBound *
          (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal ≤
          (F.card : ℝ) * (iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal := by
        simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_ofReal hlowerBound.le] using hreal
      have hdiv : (iidSequenceLaw ν
            (sourceBaseCorridorEvent (scale n) n)).toReal ≤
          ((F.card : ℝ) * (iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) /
              lowerBound := by
        apply (le_div_iff₀ hlowerBound).2
        simpa [mul_comm] using hreal'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv)
    hbaseReal htarget htargetZero δ hδ

/-- The source's widened endpoint corridor has probability tending to zero
under the stable-domain endpoint upper bound, once the two-scale hypothesis
makes the number of complete stable blocks diverge. -/
theorem tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 0 < α) (hstable : IsStrictlyAlphaStable α μ)
    (hα₂ : α < 2)
    {normalization scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    {ell : ℝ} (hell : 0 < ell)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (𝓝 ell))
    (ε c b : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0) := by
  classical
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
      (fun n => (fun _ : ℕ => 0)
        (stableBlockLength α ν 1 wideScale n) / wideScale n)
      atTop (𝓝 0) := by
    simp
  obtain ⟨q, hq0, hq1, hupper⟩ :=
    eventually_horizontalTubeProbability_le_pow_of_strictStableDomain
      ν μ hstable hα₂ hC hnorm hwideTop hDOA hcenter
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  let block : ℕ → ℕ := stableBlockLength α ν C wideScale
  have hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (wideScale n) ∧
        stableSlowVariation α ν (wideScale n) ≤ ell + 1 := by
    have hwindow : Set.Ioo (ell / 2) (ell + 1) ∈ 𝓝 ell :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [hwideTop.eventually (hslow.eventually hwindow)] with n hn
    exact ⟨by linarith, by linarith⟩
  have hblockPos : ∀ᶠ n in atTop, 0 < block n := by
    simpa [block] using eventually_stableBlockLength_pos
      hα hC (by linarith : 0 < ell + 1) hwideTop hvariation
  -- Prove the rate estimate directly.  `IsSmallDeviationScale` is an opaque
  -- definition across this module boundary, so constructing a scaled instance
  -- just to invoke the packaged lemma is not available here.
  have hnormL : Tendsto
      (fun n => stableSlowVariation α ν (normalization n)) atTop (𝓝 ell) :=
    hslow.comp hnorm.2.1
  have hwideL : Tendsto
      (fun n => stableSlowVariation α ν (wideScale n)) atTop (𝓝 ell) :=
    hslow.comp hwideTop
  have hratioPow : Tendsto (fun n => (wideScale n / normalization n) ^ α)
      atTop (𝓝 0) := hwideDiv.rpow_const_nhds_zero hα
  have hnormFactor : Tendsto
      (fun n => normalization n ^ α /
        stableSlowVariation α ν (normalization n) / (n : ℝ)) atTop (𝓝 1) :=
    hnorm.2.2
  have hslowRatio : Tendsto
      (fun n => stableSlowVariation α ν (normalization n) /
        stableSlowVariation α ν (wideScale n)) atTop (𝓝 1) := by
    have h := hnormL.div hwideL hell.ne'
    have hfun : (fun n => stableSlowVariation α ν (normalization n)) /
        (fun n => stableSlowVariation α ν (wideScale n)) =
          (fun n => stableSlowVariation α ν (normalization n) /
            stableSlowVariation α ν (wideScale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hell.ne'] using h
  have hrateProduct : Tendsto
      (fun n => (wideScale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (wideScale n))) atTop (𝓝 0) := by
    simpa using (hratioPow.mul hnormFactor).mul hslowRatio
  have hnormPos : ∀ᶠ n in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnorm.1 n hn
  have hnormLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (normalization n) := by
    filter_upwards [hnormL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have hwideLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (wideScale n) := by
    filter_upwards [hwideL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have heqRate : stableSmallDeviationRate α ν wideScale =ᶠ[atTop]
      fun n => (wideScale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (wideScale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hwideTop.eventually
        (eventually_gt_atTop 0), hnormPos, hnormLPos, hwideLPos]
      with n hn hwidePos hnormPosN hnormLp hwideLp
    rw [stableSmallDeviationRate]
    rw [Real.div_rpow (le_of_lt hwidePos) (le_of_lt hnormPosN) α]
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnormNe : normalization n ≠ 0 := hnormPosN.ne'
    have hwidePowNe : wideScale n ^ α ≠ 0 :=
      (Real.rpow_pos_of_pos hwidePos α).ne'
    have hnormPowNe : normalization n ^ α ≠ 0 :=
      (Real.rpow_pos_of_pos hnormPosN α).ne'
    field_simp [hnNe, hnormNe, hnormLp.ne', hwideLp.ne',
      hwidePowNe, hnormPowNe]
  have hrate : Tendsto (stableSmallDeviationRate α ν wideScale) atTop (𝓝 0) :=
    hrateProduct.congr' heqRate.symm
  have hblockDivZero : Tendsto (fun n => (block n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [block] using tendsto_stableBlockLength_div_nat_zero
      hα hC (by linarith : 0 < ell + 1) hwideTop hvariation hrate
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

/-- Source equation (34), followed by the logarithmic-ratio conclusion.

The bridge limit is supplied in the existing variable-block stable path-law
interface. The finite-prefix cover, the source bridge cells, their IID path
identification, and the finite-cell gluing are proved above. Base-corridor
positivity follows from the existing stable-domain return lower bound; target
decay follows from the strict-stable endpoint upper bound when `L*` has a
positive finite limit. The only index-specific entrance premise is retained
for `α < 1`, where the proof currently lives in the legacy non-module
`ShiftComparison/PoissonEntrance.lean`. -/
theorem exists_source_equation34_log_ratio_lower_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₂ : α < 2)
    {ell : ℝ} (hell : 0 < ell)
    (hslowLimit : Tendsto (stableSlowVariation α ν) atTop (𝓝 ell))
    (ε c b : ℝ) (hε : 0 < ε) (hc : -1 < c)
    (hcb : c < b) (hb : b < 1)
    (bridgeLength : ℕ → ℕ)
    (hscaleAll : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)))
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
    tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain
      ν μ hα hP.strictlyStable hα₂ hnorm hDOA hscale
      (ell := ell) hell hslowLimit ε c b hε
  have hratio := eventually_one_sub_le_log_ratio_of_source_equation34
    F hF lowerBound hlowerBound ε c b scale hcomparison hbase htargetZero δ hδ
  exact ⟨F, lowerBound, hF, hlowerBound, hratio⟩



end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
