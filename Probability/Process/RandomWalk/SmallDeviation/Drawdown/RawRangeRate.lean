/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.RangeRateBlock
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Scaling

/-!
# Raw increment-law drawdown bounds

The finite spatial-bin argument converts a one-block oscillation bound into
a drawdown-and-endpoint bound. This module supplies that composition from the
raw finite-variance Mogul'skii range rate, without a Brownian-process witness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A raw increment-law range-rate estimate yields an endpoint drawdown
estimate whenever the number of blocks covers the horizon asymptotically,
the spatial-bin count is fixed, and the block scale is aligned with the
drawdown width. `blockCost` and `totalCost` are normalized by the square of
that width. -/
theorem eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_rangeRate
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {horizon blocks length : ℕ → ℕ}
    {delta width threshold : ℕ → ℝ} (K k : ℕ)
    {factor eta rangeRate targetRate : ℝ}
    (hfactor : 1 < factor) (heta : 0 < eta)
    (hrangeRate : 0 < rangeRate)
    (hk : 0 < k)
    (hrangeRate_lt : rangeRate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy)
    (htargetRate : 0 < targetRate)
    (hlength : Tendsto (fun n => length n + 1) atTop atTop)
    (hblocks : Tendsto blocks atTop atTop)
    (hblockCost : Tendsto
      (fun n => ((length n + 1 : ℕ) : ℝ) / delta n ^ 2) atTop atTop)
    (htotalCost : Tendsto
      (fun n => (horizon n : ℝ) / delta n ^ 2) atTop atTop)
    (hcovered : Tendsto
      (fun n => (blocks n : ℝ) *
        (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) /
          ((horizon n : ℝ) / delta n ^ 2)) atTop (𝓝 1))
    (hcomplete : ∀ᶠ n : ℕ in atTop,
      blocks n * length n ≤ horizon n)
    (hwidth : ∀ᶠ n : ℕ in atTop, width n = eta * delta n)
    (hthreshold : ∀ᶠ n : ℕ in atTop,
      ⌊(threshold n + delta n) / width n⌋₊ = K)
    (hscaleBlock : ∀ᶠ n : ℕ in atTop,
      scale (length n + 1) = (factor * (1 + eta) / 2) * delta n)
    (hgap : targetRate < rangeRate / (factor * (1 + eta) / 2) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (threshold n)) ≤
        ENNReal.ofReal (Real.exp
          (-targetRate * ((horizon n : ℝ) / delta n ^ 2))) := by
  let beta : ℝ := factor * (1 + eta) / 2
  let blockCost : ℕ → ℝ := fun n =>
    ((length n + 1 : ℕ) : ℝ) / delta n ^ 2
  let totalCost : ℕ → ℝ := fun n =>
    (horizon n : ℝ) / delta n ^ 2
  let effectiveRate : ℝ := rangeRate / beta ^ 2
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have heffective : 0 < effectiveRate := div_pos hrangeRate (sq_pos_of_pos hbeta)
  have hbetaEq : beta = factor * (1 + eta) / 2 := rfl
  have hgap' : targetRate < effectiveRate := by
    simpa [effectiveRate, beta] using hgap
  have hblockCost' : Tendsto blockCost atTop atTop := by
    simpa [blockCost] using hblockCost
  have htotalCost' : Tendsto totalCost atTop atTop := by
    simpa [totalCost] using htotalCost
  have hcovered' : Tendsto (fun n => (blocks n : ℝ) * blockCost n /
      totalCost n) atTop (𝓝 1) := by
    simpa [blockCost, totalCost] using hcovered
  have hentropy := eventually_finitePatternEntropyCondition_of_scaled_rate_gap
    (K := K) hblocks hblockCost' htotalCost' hcovered' hgap'
  have hblock :=
    eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_rangeRate_reindex
      ν hcentered hsquare hvariance hscale hlength hfactor heta hrangeRate k hk
      hrangeRate_lt (by simpa [beta] using hscaleBlock)
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n := by
    have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale (length n + 1) :=
      hlength.eventually (Asymptotics.IsSmallDeviationScale.eventually_pos hscale)
    filter_upwards [hscalePos, hscaleBlock] with n hs hrel
    have hprod : 0 < beta * delta n := by
      have hprod' : 0 < (factor * (1 + eta) / 2) * delta n := by
        rw [← hrel]
        exact hs
      simpa [beta] using hprod'
    by_contra hnot
    have hδ : delta n ≤ 0 := le_of_not_gt hnot
    have hnonpos : beta * delta n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbeta.le hδ
    linarith
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n := by
    filter_upwards [hdeltaPos, hwidth] with n hδ hw
    rw [hw]
    exact mul_pos heta hδ
  have hKblocks : ∀ᶠ n : ℕ in atTop, K + 1 ≤ blocks n :=
    hblocks.eventually (eventually_ge_atTop (K + 1))
  filter_upwards [hblock, hentropy, hcomplete, hwidthPos, hwidth, hthreshold,
    hKblocks, hdeltaPos, hblockCost.eventually (eventually_gt_atTop 0),
    htotalCost.eventually (eventually_gt_atTop 0), hscaleBlock] with n hblockn hentropyn
      hcompleten hwidthPositive hwidthEqAt hthresholdn hKblock hδ
      hblockCostPos htotalCostPos hscaleBlockn
  have hoscillation :
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length n) increment ∈
          blockOscillationEvent (width n + delta n) (length n)} ≤
        ENNReal.ofReal (Real.exp (-effectiveRate * blockCost n)) := by
    have hwidthEq : width n + delta n = (1 + eta) * delta n := by
      rw [hwidthEqAt]
      ring
    have hrateEq : rangeRate / (factor * (1 + eta) / 2) ^ 2 =
        effectiveRate := by
      change rangeRate / (factor * (1 + eta) / 2) ^ 2 =
        rangeRate / beta ^ 2
      rw [hbetaEq]
    have hcostEq : rangeRate / (factor * (1 + eta) / 2) ^ 2 *
        (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) =
        effectiveRate * blockCost n := by
      calc
        _ = effectiveRate * (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) := by
          rw [hrateEq]
        _ = effectiveRate * blockCost n := by simp [blockCost]
    have hcostEqNeg :
        -(rangeRate / (factor * (1 + eta) / 2) ^ 2) *
            (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) =
          -effectiveRate * blockCost n := by
      calc
        _ = -(rangeRate / (factor * (1 + eta) / 2) ^ 2 *
            (((length n + 1 : ℕ) : ℝ) / delta n ^ 2)) := by ring
        _ = -(effectiveRate * blockCost n) := congrArg Neg.neg hcostEq
        _ = _ := by ring
    have hexpEq := congrArg Real.exp hcostEqNeg
    rw [hwidthEq]
    rw [hexpEq]
    exact hblockn
  have hunion := iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le
    (ν := ν) (q := blocks n) (K := K) (length := length n)
    (width n + delta n) hKblock
  have hsubset0 := noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent
    (horizon := horizon n) (blocks := blocks n) (blockLength := length n)
    (delta n) (width n) (threshold n) hwidthPositive hcompleten
  have hsubset : noLargeDropEndpointBelowEvent
      (horizon n) (delta n) (threshold n) ⊆
      monotoneSpatialBinPatternUnionEvent
        (q := blocks n) (K := K) (width n + delta n) (length n) := by
    simpa [hthresholdn] using hsubset0
  calc
    iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (threshold n)) ≤
      iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := blocks n) (K := K) (width n + delta n) (length n)) :=
      measure_mono hsubset
    _ ≤ ((K + 1) ^ (blocks n + 1) : ℝ≥0∞) *
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (length n) increment ∈
            blockOscillationEvent (width n + delta n) (length n)}) ^
          (blocks n - (K + 1)) := hunion
    _ ≤ ((K + 1) ^ (blocks n + 1) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-effectiveRate * blockCost n)) ^
          (blocks n - (K + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left' hoscillation (blocks n - (K + 1))) (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-targetRate * totalCost n)) := by
      simpa [totalCost] using hentropyn

/-- The raw range-rate endpoint estimate is invariant under standard-
deviation normalization.  For a centered law of variance `sigma ^ 2`, the
exponential rate is multiplied by that variance. -/
theorem eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_rangeRate_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {horizon blocks length : ℕ → ℕ}
    {delta width threshold : ℕ → ℝ} (K k : ℕ)
    {factor eta rangeRate targetRate : ℝ}
    (hfactor : 1 < factor) (heta : 0 < eta)
    (hrangeRate : 0 < rangeRate)
    (hk : 0 < k)
    (hrangeRate_lt : rangeRate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy)
    (htargetRate : 0 < targetRate)
    (hlength : Tendsto (fun n => length n + 1) atTop atTop)
    (hblocks : Tendsto blocks atTop atTop)
    (hblockCost : Tendsto
      (fun n => ((length n + 1 : ℕ) : ℝ) / delta n ^ 2) atTop atTop)
    (htotalCost : Tendsto
      (fun n => (horizon n : ℝ) / delta n ^ 2) atTop atTop)
    (hcovered : Tendsto
      (fun n => (blocks n : ℝ) *
        (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) /
          ((horizon n : ℝ) / delta n ^ 2)) atTop (𝓝 1))
    (hcomplete : ∀ᶠ n : ℕ in atTop,
      blocks n * length n ≤ horizon n)
    (hwidth : ∀ᶠ n : ℕ in atTop, width n = eta * delta n)
    (hthreshold : ∀ᶠ n : ℕ in atTop,
      ⌊(threshold n + delta n) / width n⌋₊ = K)
    (hscaleBlock : ∀ᶠ n : ℕ in atTop,
      scale (length n + 1) = (factor * (1 + eta) / 2) * delta n)
    (hgap : targetRate < rangeRate / (factor * (1 + eta) / 2) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (threshold n)) ≤
        ENNReal.ofReal (Real.exp
          (-targetRate * sigma ^ 2 * ((horizon n : ℝ) / delta n ^ 2))) := by
  let scaleUnit : ℕ → ℝ := fun n => scale n / sigma
  let deltaUnit : ℕ → ℝ := fun n => delta n / sigma
  let widthUnit : ℕ → ℝ := fun n => width n / sigma
  let thresholdUnit : ℕ → ℝ := fun n => threshold n / sigma
  let νUnit : Measure ℝ := ν.map fun x : ℝ => x / sigma
  have hνUnit : IsCenteredUnitSecondMoment νUnit := by
    simpa [νUnit] using hν.map_div hsigma
  change (∫ x : ℝ, x ∂νUnit) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂νUnit) = 1 at hνUnit
  rcases hνUnit with ⟨hcentered, hvariance⟩
  have hsquare : Integrable (fun x : ℝ => x ^ 2) νUnit :=
    Integrable.of_integral_ne_zero (by rw [hvariance]; norm_num)
  have hscaleUnit : Asymptotics.IsSmallDeviationScale scaleUnit
      (fun n => Real.sqrt n) := by
    apply Asymptotics.IsSmallDeviationScale.of_tendsto
    · have h := (Asymptotics.IsSmallDeviationScale.tendsto_atTop hscale).const_mul_atTop
        (inv_pos.mpr hsigma)
      simpa [scaleUnit, div_eq_mul_inv, mul_comm] using h
    · have h := (Asymptotics.IsSmallDeviationScale.tendsto_div hscale).div_const sigma
      have heq : (fun n : ℕ => scaleUnit n / Real.sqrt n) =ᶠ[atTop]
          fun n => (scale n / Real.sqrt n) / sigma := by
        filter_upwards with n
        dsimp [scaleUnit]
        ring
      simpa using h.congr' heq.symm
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n := by
    have hscalePos := hlength.eventually
      (Asymptotics.IsSmallDeviationScale.eventually_pos hscale)
    have hbeta : 0 < factor * (1 + eta) / 2 := by positivity
    filter_upwards [hscalePos, hscaleBlock] with n hs hrel
    have hprod : 0 < (factor * (1 + eta) / 2) * delta n := by
      rw [← hrel]
      exact hs
    by_contra hnot
    have hδ : delta n ≤ 0 := le_of_not_gt hnot
    have hprod' : (factor * (1 + eta) / 2) * delta n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbeta.le hδ
    linarith
  let blockCost : ℕ → ℝ := fun n =>
    ((length n + 1 : ℕ) : ℝ) / delta n ^ 2
  let totalCost : ℕ → ℝ := fun n => (horizon n : ℝ) / delta n ^ 2
  let blockCostUnit : ℕ → ℝ := fun n =>
    ((length n + 1 : ℕ) : ℝ) / deltaUnit n ^ 2
  let totalCostUnit : ℕ → ℝ := fun n =>
    (horizon n : ℝ) / deltaUnit n ^ 2
  have hblockCostUnitEq : blockCostUnit =ᶠ[atTop]
      fun n => sigma ^ 2 * blockCost n := by
    filter_upwards [hdeltaPos] with n hδ
    have hδne : delta n ≠ 0 := ne_of_gt hδ
    dsimp [blockCostUnit, blockCost, deltaUnit]
    field_simp [hδne, hsigma.ne']
  have htotalCostUnitEq : totalCostUnit =ᶠ[atTop]
      fun n => sigma ^ 2 * totalCost n := by
    filter_upwards [hdeltaPos] with n hδ
    have hδne : delta n ≠ 0 := ne_of_gt hδ
    dsimp [totalCostUnit, totalCost, deltaUnit]
    field_simp [hδne, hsigma.ne']
  have hblockCostUnit : Tendsto blockCostUnit atTop atTop := by
    have h := hblockCost.const_mul_atTop (sq_pos_of_pos hsigma)
    exact h.congr' hblockCostUnitEq.symm
  have htotalCostUnit : Tendsto totalCostUnit atTop atTop := by
    have h := htotalCost.const_mul_atTop (sq_pos_of_pos hsigma)
    exact h.congr' htotalCostUnitEq.symm
  have hcoveredUnit : Tendsto (fun n => (blocks n : ℝ) * blockCostUnit n /
      totalCostUnit n) atTop (𝓝 1) := by
    have hEq : (fun n => (blocks n : ℝ) * blockCostUnit n /
        totalCostUnit n) =ᶠ[atTop]
        fun n => (blocks n : ℝ) * blockCost n / totalCost n := by
      filter_upwards [hdeltaPos,
        htotalCost.eventually (eventually_gt_atTop 0)] with n hδ hcostPos
      have hδne : delta n ≠ 0 := ne_of_gt hδ
      have hblock : blockCostUnit n = sigma ^ 2 * blockCost n := by
        dsimp [blockCostUnit, blockCost, deltaUnit]
        field_simp [hδne, hsigma.ne']
      have htotal : totalCostUnit n = sigma ^ 2 * totalCost n := by
        dsimp [totalCostUnit, totalCost, deltaUnit]
        field_simp [hδne, hsigma.ne']
      have hcost : totalCost n ≠ 0 := ne_of_gt hcostPos
      rw [hblock, htotal]
      field_simp [hsigma.ne', hcost]
    exact hcovered.congr' hEq.symm
  have hwidthUnit : ∀ᶠ n : ℕ in atTop,
      widthUnit n = eta * deltaUnit n := by
    filter_upwards [hwidth] with n hn
    dsimp [widthUnit, deltaUnit]
    rw [hn]
    ring
  have hthresholdUnit : ∀ᶠ n : ℕ in atTop,
      ⌊(thresholdUnit n + deltaUnit n) / widthUnit n⌋₊ = K := by
    filter_upwards [hthreshold, hwidth, hdeltaPos] with n hn hw hδ
    have hwpos : 0 < width n := by rw [hw]; exact mul_pos heta hδ
    have hwne : width n ≠ 0 := ne_of_gt hwpos
    have hratio : (thresholdUnit n + deltaUnit n) / widthUnit n =
        (threshold n + delta n) / width n := by
      dsimp [thresholdUnit, deltaUnit, widthUnit]
      field_simp [hsigma.ne', hwne]
    rw [hratio, hn]
  have hscaleBlockUnit : ∀ᶠ n : ℕ in atTop,
      scaleUnit (length n + 1) = (factor * (1 + eta) / 2) * deltaUnit n := by
    filter_upwards [hscaleBlock] with n hn
    dsimp [scaleUnit, deltaUnit]
    rw [hn]
    field_simp [hsigma.ne']
  have hunit :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_rangeRate
      (ν := νUnit) hcentered hsquare hvariance hscaleUnit
      (length := length) (delta := deltaUnit) (width := widthUnit)
      (threshold := thresholdUnit) K k hfactor heta hrangeRate hk
      hrangeRate_lt htargetRate hlength hblocks hblockCostUnit
      htotalCostUnit hcoveredUnit hcomplete hwidthUnit hthresholdUnit
      hscaleBlockUnit hgap
  have hmeasureEq (n : ℕ) :
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (threshold n)) =
      iidSequenceLaw νUnit (noLargeDropEndpointBelowEvent
        (horizon n) (deltaUnit n) (thresholdUnit n)) := by
    exact iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div
      hsigma (horizon n) (delta n) (threshold n)
  have hexponentEq : (fun n : ℕ => -targetRate *
      ((horizon n : ℝ) / deltaUnit n ^ 2)) =ᶠ[atTop]
      fun n => -targetRate * sigma ^ 2 * totalCost n := by
    filter_upwards [hdeltaPos] with n hδ
    have hδne : delta n ≠ 0 := ne_of_gt hδ
    dsimp [deltaUnit, totalCost]
    field_simp [hδne, hsigma.ne']
  filter_upwards [hunit, hexponentEq] with n hn hexponent
  rw [hmeasureEq n, ← hexponent]
  exact hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
