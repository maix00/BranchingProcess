/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionUpper
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SourcePartitionEvents
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePartitionLower.EnergyLower

/-! # Stable upper rates for source-convention corridors -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

theorem limsup_scaledLog_sourceNormalizedStepCorridor_le_selectedCellRates
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (lo i : EReal))
    (hupper : ∀ i ∈ s,
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (hi i : EReal))
    (margin cellSlack : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    {aggregateSlack : ℝ}
    (hmargin : ∀ i ∈ s, 0 < margin i)
    (hcellSlack : ∀ i ∈ s, 0 < cellSlack i)
    (haggregateSlack : 0 < aggregateSlack)
    (hwidth : ∀ i ∈ s, 0 < hi i - lo i)
    (hnegative : ∀ i ∈ s,
      C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i < 0)
    (hcorridorPositive : ∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower})
    (hcorridorCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n * Real.log
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}).toReal)) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}).toReal) ≤
      (∑ i ∈ s,
        ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) -
          StepBoundary.commonPartitionGrid upper lower i.val) *
          (C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i)) +
        aggregateSlack := by
  let corridorProbability : ℕ → ENNReal := fun n =>
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}
  let cellProbability : Fin ((StepBoundary.commonKnots upper lower).card - 1) →
      ℕ → ENNReal := fun i n =>
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
      ((hi i - lo i) * scale n)
      (commonPartitionCellStepLength n upper lower i - 1)
  let corridorRate : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n *
      Real.log (corridorProbability n).toReal
  let cellRate : Fin ((StepBoundary.commonKnots upper lower).card - 1) →
      ℕ → ℝ := fun i n =>
    stableSmallDeviationRate α ν scale n *
      Real.log (cellProbability i n).toReal
  let cellRateLimit : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
    fun i =>
      (((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) : ℝ) -
        StepBoundary.commonPartitionGrid upper lower i.val) *
        (C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i)
  have hcellInputs : ∀ i ∈ s,
      (∀ᶠ n : ℕ in atTop, 0 < cellProbability i n) ∧
        Filter.IsCoboundedUnder (· ≤ ·) atTop (cellRate i) := by
    intro i hi
    have hhorizon : ∀ᶠ n : ℕ in atTop,
        commonPartitionCellStepLength n upper lower i - 1 ≤ n :=
      Filter.Eventually.of_forall fun n =>
        (Nat.sub_le _ _).trans (commonPartitionCellStepLength_le n upper lower i)
    simpa [cellProbability, cellRate] using
      ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_partialSumRangeOscillationLTProbability_pos_and_rateLog_cobounded
        hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
        (hwidth i hi) hhorizon
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscale.eventually_scale_pos
  have hlengthPos : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ s, 0 < commonPartitionCellStepLength n upper lower i :=
    (Finset.eventually_all s).2 fun i hi =>
      eventually_commonPartitionCellStepLength_pos upper lower i
  have hproduct : ∀ᶠ n : ℕ in atTop,
      corridorProbability n ≤ ∏ i ∈ s, cellProbability i n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hlengthPos]
      with n hn hs hlen
    simpa [corridorProbability, cellProbability, mul_comm] using
      ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete.iidSequenceLaw_sourceNormalizedStepCorridor_le_selectedCellRangeProduct
        ν hn hs upper lower s lo hi hlower hupper hlen
  have hcorridorLeOne (n : ℕ) : corridorProbability n ≤ 1 := by
    calc
      corridorProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcellLeOne (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
      (n : ℕ) : cellProbability i n ≤ 1 := by
    calc
      cellProbability i n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hrateNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ stableSmallDeviationRate α ν scale n := by
    have hscaleTop := hscale.scale_tendsto_atTop
    have hslowPos : ∀ᶠ n : ℕ in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
      hslowPos] with n hn hs hL
    rw [stableSmallDeviationRate]
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hcellPositiveAll : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ s, 0 < cellProbability i n :=
    (Finset.eventually_all s).2 fun i hi => by
      simpa [cellProbability] using (hcellInputs i hi).1
  have hlogProduct : ∀ᶠ n : ℕ in atTop,
      Real.log (corridorProbability n).toReal ≤
        ∑ i ∈ s, Real.log (cellProbability i n).toReal := by
    filter_upwards [hproduct, hcorridorPositive, hcellPositiveAll]
      with n hprod hp hcells
    have hpTop : corridorProbability n ≠ ⊤ := by
      exact ne_of_lt (hcorridorLeOne n |>.trans_lt ENNReal.one_lt_top)
    have hprodTop : (∏ i ∈ s, cellProbability i n) ≠ ⊤ :=
      ENNReal.prod_ne_top (by
        intro i hi
        exact ne_of_lt (hcellLeOne i n |>.trans_lt ENNReal.one_lt_top))
    have hrealBound : (corridorProbability n).toReal ≤
        (∏ i ∈ s, cellProbability i n).toReal :=
      (ENNReal.toReal_le_toReal hpTop hprodTop).2 hprod
    have hpRealPos : 0 < (corridorProbability n).toReal :=
      ENNReal.toReal_pos (ne_of_gt hp) hpTop
    have hcellRealPos (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
        (hi : i ∈ s) : 0 < (cellProbability i n).toReal := by
      exact ENNReal.toReal_pos (ne_of_gt (hcells i hi))
        (ne_of_lt (hcellLeOne i n |>.trans_lt ENNReal.one_lt_top))
    have hlog := Real.log_le_log hpRealPos hrealBound
    rw [ENNReal.toReal_prod,
      Real.log_prod (fun i hi => ne_of_gt (hcellRealPos i hi))] at hlog
    exact hlog
  have hrateLeCellRates : ∀ᶠ n : ℕ in atTop,
      corridorRate n ≤ ∑ i ∈ s, cellRate i n := by
    filter_upwards [hlogProduct, hrateNonneg] with n hlog hrate
    have hmul := mul_le_mul_of_nonneg_left hlog hrate
    simpa [corridorRate, cellRate, cellProbability, Finset.mul_sum] using hmul
  have hcellRateBounded (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
      (hi : i ∈ s) : Filter.IsBoundedUnder (· ≤ ·) atTop (cellRate i) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 0)
    filter_upwards [(hcellInputs i hi).1, hrateNonneg] with n hpos hrate
    have hqTop : cellProbability i n ≠ ⊤ :=
      ne_of_lt (hcellLeOne i n |>.trans_lt ENNReal.one_lt_top)
    have hqRealPos : 0 < (cellProbability i n).toReal :=
      ENNReal.toReal_pos (ne_of_gt hpos) hqTop
    have hqRealLe : (cellProbability i n).toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hqTop ENNReal.one_ne_top).2 (hcellLeOne i n)
    have hlog : Real.log (cellProbability i n).toReal ≤ 0 :=
      Real.log_nonpos (le_of_lt hqRealPos) hqRealLe
    dsimp [cellRate]
    exact mul_nonpos_of_nonneg_of_nonpos hrate hlog
  have hcellRateLimit (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
      (hi : i ∈ s) : atTop.limsup (cellRate i) ≤ cellRateLimit i := by
    simpa [cellRate, cellProbability, cellRateLimit] using
      limsup_commonPartitionCellRangeProbability_le_of_escapeRate
        hscale hα hα₂ hslow hEscape hDOA htightBase upper lower i
        (hwidth i hi) (hmargin i hi) (hcellSlack i hi)
        (hnegative i hi) (by simpa [cellProbability] using (hcellInputs i hi).1)
        (by simpa [cellRate, cellProbability] using (hcellInputs i hi).2)
  let δ : ℝ := aggregateSlack / ((s.card : ℝ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hcellNear : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ s, cellRate i n < cellRateLimit i + δ :=
    (Finset.eventually_all s).2 fun i hi =>
      Filter.eventually_lt_add_pos_of_limsup_le
        (hcellRateBounded i hi) (hcellRateLimit i hi) hδ
  have hcardδ : (s.card : ℝ) * δ ≤ aggregateSlack := by
    dsimp [δ]
    have hden : 0 < (s.card : ℝ) + 1 := by positivity
    have hratio : (s.card : ℝ) / ((s.card : ℝ) + 1) ≤ 1 := by
      apply (div_le_one hden).2
      have hcard : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
      linarith
    calc
      (s.card : ℝ) * (aggregateSlack / ((s.card : ℝ) + 1)) =
          aggregateSlack * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by ring
      _ ≤ aggregateSlack * 1 :=
        mul_le_mul_of_nonneg_left hratio haggregateSlack.le
      _ = aggregateSlack := by ring
  have heventual : ∀ᶠ n : ℕ in atTop,
      corridorRate n ≤ (∑ i ∈ s, cellRateLimit i) + aggregateSlack := by
    filter_upwards [hcellNear, hrateLeCellRates] with n hnear hrate
    have hsum : (∑ i ∈ s, cellRate i n) ≤
        (∑ i ∈ s, cellRateLimit i) + (s.card : ℝ) * δ := by
      calc
        (∑ i ∈ s, cellRate i n) ≤ ∑ i ∈ s, (cellRateLimit i + δ) :=
          Finset.sum_le_sum fun i hi => (hnear i hi).le
        _ = (∑ i ∈ s, cellRateLimit i) + (s.card : ℝ) * δ := by
          rw [Finset.sum_add_distrib]
          simp [nsmul_eq_mul]
    exact hrate.trans (by linarith [hsum, hcardδ])
  exact Filter.limsup_le_of_le hcorridorCobounded heventual

/-- The source-convention selected-cell estimate specializes to an `M₂`
corridor. The source lower energy theorem supplies eventual positivity and a
finite lower bound for the logarithmic rate. -/
theorem limsup_scaledLog_sourceNormalizedStepCorridor_le_selectedCellRates_of_M2
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : M2Corridor)
    (s : Finset (Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s,
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) =
        (lo i : EReal))
    (hupper : ∀ i ∈ s,
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) =
        (hi i : EReal))
    (margin cellSlack : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ)
    {aggregateSlack : ℝ}
    (hmargin : ∀ i ∈ s, 0 < margin i)
    (hcellSlack : ∀ i ∈ s, 0 < cellSlack i)
    (haggregateSlack : 0 < aggregateSlack)
    (hwidth : ∀ i ∈ s, 0 < hi i - lo i)
    (hnegative : ∀ i ∈ s,
      C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i < 0) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
            c.upper c.lower}).toReal) ≤
      (∑ i ∈ s,
        ((StepBoundary.commonPartitionGrid c.upper c.lower (i.val + 1) : unitInterval) -
          StepBoundary.commonPartitionGrid c.upper c.lower i.val) *
          (C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i)) +
        aggregateSlack := by
  let corridorProbability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
          c.upper c.lower}
  have hlowerBound :=
    eventually_stableSmallDeviationRate_mul_log_sourceNormalizedStepCorridor_ge_energy
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
      (error := 1) (by norm_num)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < corridorProbability n := by
    filter_upwards [hlowerBound] with n hn
    simpa [corridorProbability] using hn.1
  have hcobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n *
        Real.log (corridorProbability n).toReal) :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := C * 2 ^ α * (c.energy α).toReal - 1)
      (Filter.Eventually.frequently (hlowerBound.mono fun n hn => by
        simpa only [corridorProbability] using hn.2))
  exact limsup_scaledLog_sourceNormalizedStepCorridor_le_selectedCellRates
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
    c.upper c.lower s lo hi hlower hupper margin cellSlack hmargin hcellSlack
    haggregateSlack hwidth hnegative hpositive hcobounded

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
