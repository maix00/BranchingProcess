/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLower.FiniteProduct
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLower.BridgeProduct
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerGeometry
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

/-!
# Positivity and logarithmic coboundedness for finite corridors.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- Start admissibility and trace separation suffice to choose endpoint cores
and local bridge windows, so every finite strict step corridor has positive
probability for all sufficiently large horizons. The local margins are
chosen from the positive geometric slacks, rather than being additional
probabilistic assumptions. -/
theorem eventually_iidSequenceLaw_normalizedStepCorridor_pos
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
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) :
    (∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}) ∧
    Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => stableSmallDeviationRate α ν scale n *
        Real.log (iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
            ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}).toReal) := by
  classical
  obtain ⟨center, radius, innerLower, innerUpper,
      hcenter0, hradius0, hradiusStep, hcores, hgeometry⟩ :=
    exists_commonPartitionLowerGeometry upper lower hstart hsep
  let cellIndex := Fin ((StepBoundary.commonKnots upper lower).card - 1)
  let left (i : cellIndex) := commonPartitionCellLeftKnotIndex upper lower i
  let right (i : cellIndex) := commonPartitionCellRightKnotIndex upper lower i
  let lower0 (i : cellIndex) := innerLower i + radius (left i) - center (left i)
  let upper0 (i : cellIndex) := innerUpper i - radius (left i) - center (left i)
  let displacement (i : cellIndex) := center (right i) - center (left i)
  let radiusIncrease (i : cellIndex) := radius (right i) - radius (left i)
  let slack (i : cellIndex) :=
    min (-lower0 i) (min (upper0 i)
      (min (displacement i - lower0 i)
        (min (upper0 i - displacement i) (radiusIncrease i))))
  let margin (i : cellIndex) := slack i / 4
  let epsilon (i : cellIndex) := slack i / 32
  let delta (_i : cellIndex) := (1 : ℝ)
  let cellLower (i : cellIndex) := lower0 i + margin i
  let cellUpper (i : cellIndex) := upper0 i - margin i
  have hlower0 (i : cellIndex) : lower0 i < 0 := by
    dsimp [lower0, left]
    linarith [(hgeometry i).2.1]
  have hupper0 (i : cellIndex) : 0 < upper0 i := by
    dsimp [upper0, left]
    linarith [(hgeometry i).2.2.2.1]
  have hdisplacementLower (i : cellIndex) : lower0 i < displacement i := by
    dsimp [lower0, displacement, left, right]
    linarith [(hgeometry i).2.2.1, hradiusStep i]
  have hdisplacementUpper (i : cellIndex) :
      displacement i < upper0 i := by
    dsimp [upper0, displacement, left, right]
    linarith [(hgeometry i).2.2.2.2.1, hradiusStep i]
  have hradiusIncrease (i : cellIndex) : 0 < radiusIncrease i := by
    exact sub_pos.mpr (hradiusStep i)
  have hslackPos (i : cellIndex) : 0 < slack i := by
    dsimp [slack]
    apply lt_min
    · linarith [hlower0 i]
    · apply lt_min
      · exact hupper0 i
      · apply lt_min
        · linarith [hdisplacementLower i]
        · apply lt_min
          · linarith [hdisplacementUpper i]
          · exact hradiusIncrease i
  have hslackNeg (i : cellIndex) : slack i ≤ -lower0 i := by
    dsimp [slack]
    exact min_le_left _ _
  have hslackUpper (i : cellIndex) : slack i ≤ upper0 i := by
    dsimp [slack]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hslackBridgeLower (i : cellIndex) :
      slack i ≤ displacement i - lower0 i := by
    dsimp [slack]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hslackBridgeUpper (i : cellIndex) :
      slack i ≤ upper0 i - displacement i := by
    dsimp [slack]
    calc
      min (-lower0 i)
          (min (upper0 i)
            (min (displacement i - lower0 i)
              (min (upper0 i - displacement i) (radiusIncrease i)))) ≤
          min (upper0 i)
            (min (displacement i - lower0 i)
              (min (upper0 i - displacement i) (radiusIncrease i))) := min_le_right _ _
      _ ≤ min (displacement i - lower0 i)
            (min (upper0 i - displacement i) (radiusIncrease i)) := min_le_right _ _
      _ ≤ min (upper0 i - displacement i) (radiusIncrease i) := min_le_right _ _
      _ ≤ upper0 i - displacement i := min_le_left _ _
  have hslackRadius (i : cellIndex) : slack i ≤ radiusIncrease i := by
    dsimp [slack]
    calc
      min (-lower0 i)
          (min (upper0 i)
            (min (displacement i - lower0 i)
              (min (upper0 i - displacement i) (radiusIncrease i)))) ≤
          min (upper0 i)
            (min (displacement i - lower0 i)
              (min (upper0 i - displacement i) (radiusIncrease i))) := min_le_right _ _
      _ ≤ min (displacement i - lower0 i)
            (min (upper0 i - displacement i) (radiusIncrease i)) := min_le_right _ _
      _ ≤ min (upper0 i - displacement i) (radiusIncrease i) := min_le_right _ _
      _ ≤ radiusIncrease i := min_le_right _ _
  have hcellLowerMargin (i : cellIndex) :
      cellLower i + 8 * epsilon i < 0 := by
    dsimp [cellLower, lower0, margin, epsilon]
    nlinarith [hslackPos i, hslackNeg i]
  have hcellUpperMargin (i : cellIndex) :
      0 < cellUpper i - 8 * epsilon i := by
    dsimp [cellUpper, upper0, margin, epsilon]
    nlinarith [hslackPos i, hslackUpper i]
  have hbridgeLower (i : cellIndex) :
      cellLower i + 8 * epsilon i < displacement i := by
    dsimp [cellLower, lower0, margin, epsilon]
    nlinarith [hslackPos i, hslackBridgeLower i]
  have hbridgeUpper (i : cellIndex) :
      displacement i + 8 * epsilon i < cellUpper i := by
    dsimp [cellUpper, upper0, margin, epsilon]
    nlinarith [hslackPos i, hslackBridgeUpper i]
  have hcenter0' : ∀ j, j.val = 0 → center j = 0 := by
    intro j hj
    have hcard : 0 < (StepBoundary.commonKnots upper lower).card :=
      Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
    let root : Fin (StepBoundary.commonKnots upper lower).card := ⟨0, by omega⟩
    have hroot : j = root := Fin.ext hj
    rw [hroot]
    exact hcenter0
  have hradius0' : ∀ j, j.val = 0 → radius j = 0 := by
    intro j hj
    have hcard : 0 < (StepBoundary.commonKnots upper lower).card :=
      Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower)
    let root : Fin (StepBoundary.commonKnots upper lower).card := ⟨0, by omega⟩
    have hroot : j = root := Fin.ext hj
    rw [hroot]
    exact hradius0
  have hreturnWindows : ∀ i : cellIndex, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
      cellLower i + 4 * epsilon i < (((j : ℝ) - 1) * epsilon i) ∧
        ((j : ℝ) + 1) * epsilon i < cellUpper i - 4 * epsilon i := by
    intro i j hj
    have hj' : -3 ≤ (j : ℝ) ∧ (j : ℝ) ≤ 3 := by
      exact_mod_cast Finset.mem_Icc.mp hj
    have hleft : (-4 : ℝ) * epsilon i ≤ ((j : ℝ) - 1) * epsilon i :=
      mul_le_mul_of_nonneg_right (by linarith [hj'.1]) (le_of_lt (by
        dsimp [epsilon]
        exact div_pos (hslackPos i) (by norm_num)))
    have hright : ((j : ℝ) + 1) * epsilon i ≤ 4 * epsilon i :=
      mul_le_mul_of_nonneg_right (by linarith [hj'.2]) (le_of_lt (by
        dsimp [epsilon]
        exact div_pos (hslackPos i) (by norm_num)))
    constructor <;> linarith [hcellLowerMargin i, hcellUpperMargin i]
  have hbridgeWindows : ∀ i : cellIndex,
      cellLower i + 4 * epsilon i < displacement i - 4 * epsilon i ∧
        displacement i + 4 * epsilon i < cellUpper i - 4 * epsilon i := by
    intro i
    constructor <;> linarith [hbridgeLower i, hbridgeUpper i]
  have hendpointBand : ∀ i : cellIndex,
      3 * epsilon i < radiusIncrease i / 2 := by
    intro i
    dsimp [epsilon]
    have hle := hslackRadius i
    nlinarith [hslackPos i, hradiusIncrease i]
  have hepsilon : ∀ i : cellIndex, 0 < epsilon i := by
    intro i
    dsimp [epsilon]
    exact div_pos (hslackPos i) (by norm_num)
  have hmargin : ∀ i : cellIndex, 0 < margin i := by
    intro i
    dsimp [margin]
    exact div_pos (hslackPos i) (by norm_num)
  have hdelta : ∀ i : cellIndex, 0 < delta i := by
    intro i
    norm_num [delta]
  have hlower : ∀ i : cellIndex,
      cellLower i = innerLower i + radius (left i) + margin i - center (left i) := by
    intro i
    dsimp [cellLower, lower0, left]
    ring
  have hupper : ∀ i : cellIndex,
      cellUpper i = innerUpper i - radius (left i) - margin i - center (left i) := by
    intro i
    dsimp [cellUpper, upper0, left]
    ring
  have hendpointBand' : ∀ i : cellIndex,
      3 * epsilon i <
        (radius (right i) - radius (left i)) / 2 := by
    simpa [radiusIncrease, left, right] using hendpointBand
  have hbridgeWindows' : ∀ i : cellIndex,
      cellLower i + 4 * epsilon i < center (right i) - center (left i) - 4 * epsilon i ∧
        center (right i) - center (left i) + 4 * epsilon i <
          cellUpper i - 4 * epsilon i := by
    simpa [displacement, left, right] using hbridgeWindows
  obtain ⟨amplitude, hamplitude, hproduct⟩ :=
    exists_eventually_iidSequenceLaw_normalizedStepCorridor_lowerBound_of_endpointCoreBridges
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase upper lower center radius
      innerLower innerUpper hcenter0' hradius0' hradiusStep hcores hgeometry
      cellLower cellUpper epsilon margin delta hlower hupper hmargin hepsilon hdelta
      hendpointBand' hreturnWindows hbridgeWindows'
  let cellBound : cellIndex → ℕ → ENNReal := fun i n =>
    ENNReal.ofReal (Real.exp
      ((C / (((cellUpper i - cellLower i - 8 * epsilon i) / 2) ^ α) -
        delta i) * amplitude i ^ α)) ^
      (Asymptotics.balancedBlockCount
        (commonPartitionCellStepLength n upper lower i -
          stableBlockLength α ν (amplitude i ^ α) scale n)
        (stableBlockLength α ν (amplitude i ^ α) scale n) + 1)
  have hpositiveEvent : ∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} := by
    filter_upwards [hproduct] with n hproductN
    have hpositive : 0 < ∏ i : cellIndex, cellBound i n := by
      apply pos_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      dsimp [cellBound]
      apply pow_ne_zero
      apply ENNReal.ofReal_ne_zero_iff.mpr
      exact Real.exp_pos _
    exact lt_of_lt_of_le hpositive (by simpa [cellBound] using hproductN)
  let duration (i : cellIndex) : ℝ :=
    (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ) -
      StepBoundary.commonPartitionGrid upper lower i.val
  let coreCount (i : cellIndex) (n : ℕ) : ℕ :=
    Asymptotics.balancedBlockCount
      (commonPartitionCellStepLength n upper lower i -
        stableBlockLength α ν (amplitude i ^ α) scale n)
      (stableBlockLength α ν (amplitude i ^ α) scale n) + 1
  let exponent (i : cellIndex) : ℝ :=
    (C / (((cellUpper i - cellLower i - 8 * epsilon i) / 2) ^ α) - delta i) *
      amplitude i ^ α
  let corridorProbability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower}
  let corridorRate (n : ℕ) : ℝ :=
    stableSmallDeviationRate α ν scale n * Real.log (corridorProbability n).toReal
  let logLower (n : ℕ) : ℝ :=
    ∑ i : cellIndex,
      stableSmallDeviationRate α ν scale n * (coreCount i n : ℝ) * exponent i
  have hcountLimit (i : cellIndex) :
      Tendsto (fun n => stableSmallDeviationRate α ν scale n *
        (coreCount i n : ℝ)) atTop (nhds (duration i / amplitude i ^ α)) := by
    have hduration : 0 < duration i := by
      dsimp [duration]
      have h := StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
      exact sub_pos.mpr (by exact_mod_cast h)
    have htotal : Tendsto
        (fun n => (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ))
        atTop (nhds (duration i)) := by
      simpa [duration] using tendsto_commonPartitionCellStepLength_div_nat upper lower i
    simpa [coreCount] using
      tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount
        hα hα₂ (hamplitude i) hscale hslow hduration
        (fun n => commonPartitionCellStepLength n upper lower i) htotal
  have htermLimit (i : cellIndex) :
      Tendsto (fun n => stableSmallDeviationRate α ν scale n *
          (coreCount i n : ℝ) * exponent i)
        atTop (nhds ((duration i / amplitude i ^ α) * exponent i)) := by
    have hconst : Tendsto (fun _ : ℕ => exponent i) atTop (nhds (exponent i)) :=
      tendsto_const_nhds
    simpa [mul_assoc] using (hcountLimit i).mul hconst
  let lowerLimit : ℝ :=
    ∑ i : cellIndex, (duration i / amplitude i ^ α) * exponent i
  have hlogLowerLimit : Tendsto logLower atTop (nhds lowerLimit) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset cellIndex)
      (fun i _ => htermLimit i)
    simpa [logLower, lowerLimit] using hsum
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
  have hcorridorLeOne (n : ℕ) : corridorProbability n ≤ 1 := by
    calc
      corridorProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hlogProductLe : ∀ᶠ n : ℕ in atTop,
      logLower n ≤ corridorRate n := by
    filter_upwards [hproduct, hpositiveEvent, hrateNonneg] with n hproductN hprobPos hrate
    have hprodPos : 0 < ∏ i : cellIndex, cellBound i n := by
      apply pos_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      dsimp [cellBound]
      apply pow_ne_zero
      apply ENNReal.ofReal_ne_zero_iff.mpr
      exact Real.exp_pos _
    have hprodLe : (∏ i : cellIndex, cellBound i n) ≤ corridorProbability n := by
      simpa [corridorProbability] using hproductN
    have hprodTop : (∏ i : cellIndex, cellBound i n) ≠ ⊤ := by
      apply ne_of_lt
      exact lt_of_le_of_lt (hprodLe.trans (hcorridorLeOne n)) ENNReal.one_lt_top
    have hprobTop : corridorProbability n ≠ ⊤ :=
      ne_of_lt ((hcorridorLeOne n).trans_lt ENNReal.one_lt_top)
    have hprodRealPos : 0 < (∏ i : cellIndex, cellBound i n).toReal :=
      ENNReal.toReal_pos hprodPos.ne' hprodTop
    have hprodRealLe : (∏ i : cellIndex, cellBound i n).toReal ≤
        (corridorProbability n).toReal :=
      (ENNReal.toReal_le_toReal hprodTop hprobTop).2 hprodLe
    have hlogMono :
        Real.log (∏ i : cellIndex, cellBound i n).toReal ≤
          Real.log (corridorProbability n).toReal :=
      Real.log_le_log hprodRealPos hprodRealLe
    have hfactorPos (i : cellIndex) : 0 < (cellBound i n).toReal := by
      dsimp [cellBound]
      have hbase : 0 < ENNReal.ofReal (Real.exp (exponent i)) :=
        ENNReal.ofReal_pos.mpr (Real.exp_pos _)
      have hbaseTop : ENNReal.ofReal (Real.exp (exponent i)) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      exact ENNReal.toReal_pos (ENNReal.pow_pos hbase _).ne'
        (ENNReal.pow_ne_top hbaseTop)
    have hlogProduct : Real.log (∏ i : cellIndex, cellBound i n).toReal =
        ∑ i : cellIndex, (coreCount i n : ℝ) * exponent i := by
      rw [ENNReal.toReal_prod]
      rw [Real.log_prod (fun i _ => (hfactorPos i).ne')]
      apply Finset.sum_congr rfl
      intro i hi
      have hfactor : (cellBound i n).toReal =
          Real.exp (exponent i) ^ coreCount i n := by
        dsimp [cellBound, coreCount, exponent]
        simp [ENNReal.toReal_pow, ENNReal.toReal_ofReal, Real.exp_nonneg]
      rw [hfactor, Real.log_pow, Real.log_exp]
    have hlogLower : logLower n =
        stableSmallDeviationRate α ν scale n *
          Real.log (∏ i : cellIndex, cellBound i n).toReal := by
      rw [hlogProduct]
      dsimp [logLower]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hmul := mul_le_mul_of_nonneg_left hlogMono hrate
    dsimp [corridorRate]
    rw [hlogLower]
    exact hmul
  have hlowerEvent : ∀ᶠ n : ℕ in atTop,
      lowerLimit - 1 ≤ corridorRate n := by
    have hlt : lowerLimit - 1 < lowerLimit := by linarith
    have hnear : ∀ᶠ n : ℕ in atTop, lowerLimit - 1 < logLower n := by
      have hmem := hlogLowerLimit.eventually (isOpen_Ioi.mem_nhds hlt)
      simpa only [Set.mem_Ioi] using hmem
    filter_upwards [hnear, hlogProductLe] with n hnear hlog
    exact le_of_lt hnear |>.trans hlog
  refine ⟨hpositiveEvent, ?_⟩
  exact Filter.isCoboundedUnder_le_of_eventually_le atTop hlowerEvent


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
