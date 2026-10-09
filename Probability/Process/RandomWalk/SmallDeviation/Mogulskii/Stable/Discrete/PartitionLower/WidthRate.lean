/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLower.Positivity
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Partition.LowerApproximation
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

/-!
# Sharp lower rates for prescribed finite-partition widths.
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- For any prescribed strict inner widths, the endpoint-core product
construction gives the corresponding finite-partition lower rate, up to an
arbitrary error. The proof first chooses inner intervals wider than the
targets, then makes the return margins and the stable-process transfer loss
small enough that neither changes the target rate. -/
theorem eventually_iidSequenceLaw_normalizedStepCorridor_ge_targetRate
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
    (hsep : TraceSeparated upper lower)
    (targetWidth : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (htarget : ∀ i, 0 < targetWidth i)
    (hwidth : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      targetWidth i <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} ∧
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          ((targetWidth i / 2) ^ α)) - error ≤
        stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              Skorokhod.PathClass.StepCorridor.corridorSet upper lower}).toReal := by
  classical
  let cellIndex := Fin ((StepBoundary.commonKnots upper lower).card - 1)
  let availableGap (i : cellIndex) : ℝ :=
    if lower.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
        upper.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ then
      1
    else
      (upper.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
        (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          targetWidth i
  have havailableGapPos (i : cellIndex) : 0 < availableGap i := by
    by_cases hinfinite :
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤
    · have hinfiniteEval :
          lower.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
            upper.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ := by
        simpa [StepBoundary.rightTrace_eq_eval] using hinfinite
      simp [availableGap, hinfiniteEval]
    · rcases hwidth i with hbot | htop | hfinite
      · exact (hinfinite (Or.inl hbot)).elim
      · exact (hinfinite (Or.inr htop)).elim
      · have hinfiniteEval :
            ¬ (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
              upper.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤) := by
          intro h
          apply hinfinite
          simpa [StepBoundary.rightTrace_eq_eval] using h
        have hfiniteEval : targetWidth i <
            (upper.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
              (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal := by
          simpa [StepBoundary.rightTrace_eq_eval] using hfinite
        simp [availableGap, hinfiniteEval]
        linarith [hfiniteEval]
  let inverseGapSum : ℝ := ∑ i : cellIndex, (availableGap i)⁻¹
  let coreTolerance : ℝ := 1 / (4 * (inverseGapSum + 1))
  have hinverseGapSumNonneg : 0 ≤ inverseGapSum := by
    dsimp [inverseGapSum]
    apply Finset.sum_nonneg
    intro i hi
    exact inv_nonneg.mpr (le_of_lt (havailableGapPos i))
  have hcoreTolerance : 0 < coreTolerance := by
    dsimp [coreTolerance]
    positivity
  have hcoreToleranceSmall (i : cellIndex) :
      2 * coreTolerance < availableGap i := by
    have hterm : (availableGap i)⁻¹ ≤ inverseGapSum := by
      change (availableGap i)⁻¹ ≤
        ∑ j ∈ (Finset.univ : Finset cellIndex), (availableGap j)⁻¹
      exact Finset.single_le_sum
        (fun j hj => inv_nonneg.mpr (le_of_lt (havailableGapPos j)))
        (Finset.mem_univ i)
    have hinverse : 1 / availableGap i < inverseGapSum + 1 := by
      calc
        1 / availableGap i = (availableGap i)⁻¹ := by simp
        _ ≤ inverseGapSum := hterm
        _ < inverseGapSum + 1 := by linarith
    have hproduct : 1 < (inverseGapSum + 1) * availableGap i := by
      have h := (div_lt_iff₀ (havailableGapPos i)).mp hinverse
      nlinarith [h]
    have hden : 0 < 4 * (inverseGapSum + 1) := by positivity
    have hquarter : coreTolerance < availableGap i / 4 := by
      dsimp [coreTolerance]
      apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
      nlinarith [hproduct]
    nlinarith [hquarter, havailableGapPos i]
  let targetWidth' (i : cellIndex) := targetWidth i + 2 * coreTolerance
  have htarget' (i : cellIndex) : 0 < targetWidth' i := by
    dsimp [targetWidth']
    linarith [htarget i, hcoreTolerance]
  have hwidth' (i : cellIndex) :
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      targetWidth' i <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal := by
    by_cases hinfinite :
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤
    · rcases hinfinite with hbot | htop
      · exact Or.inl hbot
      · exact Or.inr (Or.inl htop)
    · rcases hwidth i with hbot | htop | hfinite
      · exact (hinfinite (Or.inl hbot)).elim
      · exact (hinfinite (Or.inr htop)).elim
      · right
        right
        have hinfiniteEval :
            ¬ (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
              upper.eval (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤) := by
          intro h
          apply hinfinite
          simpa [StepBoundary.rightTrace_eq_eval] using h
        have hfiniteEval : targetWidth i <
            (upper.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
              (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal := by
          simpa [StepBoundary.rightTrace_eq_eval] using hfinite
        have hgapEq : availableGap i =
            (upper.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
              (lower.eval (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
                targetWidth i := by
          simp [availableGap, hinfiniteEval]
        have hsmall := hcoreToleranceSmall i
        rw [hgapEq] at hsmall
        dsimp [targetWidth']
        linarith [hsmall, hfiniteEval]
  obtain ⟨center, radius, _innerLower0, _innerUpper0, hcenter0, hradius0,
      hradiusStep, hradiusSmall, hradiusNonneg, hcores, _hgeometry0⟩ :=
    exists_commonPartitionLowerGeometry_small upper lower hstart hsep
      hcoreTolerance
  have hcellBounds : ∀ i : cellIndex,
      ∃ lo hi : ℝ,
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
        lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        lo < center (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
          radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
          radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
        hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) ∧
        targetWidth' i < hi - lo := by
    intro i
    exact exists_commonPartitionCellInnerBounds_withWidth upper lower center radius
      hcores hradiusNonneg hradiusStep i (htarget' i) (hwidth' i)
  choose innerLower innerUpper hcellGeometry using hcellBounds
  have hgeometry : ∀ i : cellIndex,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
    intro i
    rcases hcellGeometry i with ⟨h₁, h₂, h₃, h₄, h₅, h₆, _⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  have htargetWidthInner (i : cellIndex) :
      targetWidth' i < innerUpper i - innerLower i := by
    rcases hcellGeometry i with ⟨_, _, _, _, _, _, hwidth⟩
    linarith [hwidth]
  let left (i : cellIndex) := commonPartitionCellLeftKnotIndex upper lower i
  let right (i : cellIndex) := commonPartitionCellRightKnotIndex upper lower i
  let duration (i : cellIndex) : ℝ :=
    (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ) -
      StepBoundary.commonPartitionGrid upper lower i.val
  let lower0 (i : cellIndex) := innerLower i + radius (left i) - center (left i)
  let upper0 (i : cellIndex) := innerUpper i - radius (left i) - center (left i)
  let displacement (i : cellIndex) := center (right i) - center (left i)
  let radiusIncrease (i : cellIndex) := radius (right i) - radius (left i)
  let widthGap (i : cellIndex) :=
    innerUpper i - innerLower i - targetWidth i - 2 * coreTolerance
  let coreSlack (i : cellIndex) :=
    min (-lower0 i) (min (upper0 i)
      (min (displacement i - lower0 i)
        (min (upper0 i - displacement i) (radiusIncrease i))))
  let slack (i : cellIndex) := min (coreSlack i) (widthGap i)
  let margin (i : cellIndex) := slack i / 4
  let epsilon (i : cellIndex) := slack i / 32
  let cellLower (i : cellIndex) := lower0 i + margin i
  let cellUpper (i : cellIndex) := upper0 i - margin i
  have hduration (i : cellIndex) : 0 < duration i := by
    dsimp [duration]
    have h := StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
    exact sub_pos.mpr (by exact_mod_cast h)
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
  have hradiusIncrease (i : cellIndex) : 0 < radiusIncrease i :=
    sub_pos.mpr (hradiusStep i)
  have hwidthGap (i : cellIndex) : 0 < widthGap i := by
    have h := htargetWidthInner i
    dsimp [targetWidth'] at h
    dsimp [widthGap]
    linarith [h]
  have hcoreSlackPos (i : cellIndex) : 0 < coreSlack i := by
    dsimp [coreSlack]
    apply lt_min
    · linarith [hlower0 i]
    · apply lt_min
      · exact hupper0 i
      · apply lt_min
        · linarith [hdisplacementLower i]
        · apply lt_min
          · linarith [hdisplacementUpper i]
          · exact hradiusIncrease i
  have hslackPos (i : cellIndex) : 0 < slack i :=
    lt_min (hcoreSlackPos i) (hwidthGap i)
  have hcoreSlackNeg (i : cellIndex) : coreSlack i ≤ -lower0 i := by
    dsimp [coreSlack]
    exact min_le_left _ _
  have hcoreSlackUpper (i : cellIndex) : coreSlack i ≤ upper0 i := by
    dsimp [coreSlack]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcoreSlackBridgeLower (i : cellIndex) :
      coreSlack i ≤ displacement i - lower0 i := by
    dsimp [coreSlack]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hcoreSlackBridgeUpper (i : cellIndex) :
      coreSlack i ≤ upper0 i - displacement i := by
    dsimp [coreSlack]
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
  have hcoreSlackRadius (i : cellIndex) : coreSlack i ≤ radiusIncrease i := by
    dsimp [coreSlack]
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
  have hslackNeg (i : cellIndex) : slack i ≤ -lower0 i :=
    (min_le_left _ _).trans (hcoreSlackNeg i)
  have hslackUpper (i : cellIndex) : slack i ≤ upper0 i :=
    (min_le_left _ _).trans (hcoreSlackUpper i)
  have hslackBridgeLower (i : cellIndex) :
      slack i ≤ displacement i - lower0 i :=
    (min_le_left _ _).trans (hcoreSlackBridgeLower i)
  have hslackBridgeUpper (i : cellIndex) :
      slack i ≤ upper0 i - displacement i :=
    (min_le_left _ _).trans (hcoreSlackBridgeUpper i)
  have hslackRadius (i : cellIndex) : slack i ≤ radiusIncrease i :=
    (min_le_left _ _).trans (hcoreSlackRadius i)
  have hslackGap (i : cellIndex) : slack i ≤ widthGap i := min_le_right _ _
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
    have hepsPos : 0 < epsilon i := by
      dsimp [epsilon]
      exact div_pos (hslackPos i) (by norm_num)
    have hleft : (-4 : ℝ) * epsilon i ≤ ((j : ℝ) - 1) * epsilon i :=
      mul_le_mul_of_nonneg_right (by linarith [hj'.1]) hepsPos.le
    have hright : ((j : ℝ) + 1) * epsilon i ≤ 4 * epsilon i :=
      mul_le_mul_of_nonneg_right (by linarith [hj'.2]) hepsPos.le
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
  have hmargin : ∀ i : cellIndex, 0 < margin i := by
    intro i
    dsimp [margin]
    exact div_pos (hslackPos i) (by norm_num)
  have hepsilon : ∀ i : cellIndex, 0 < epsilon i := by
    intro i
    dsimp [epsilon]
    exact div_pos (hslackPos i) (by norm_num)
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
  let effectiveHalfWidth (i : cellIndex) : ℝ :=
    (cellUpper i - cellLower i - 8 * epsilon i) / 2
  have heffectiveWidth (i : cellIndex) :
      targetWidth i < cellUpper i - cellLower i - 8 * epsilon i := by
    have hthree : 3 * slack i / 4 < widthGap i := by
      nlinarith [hslackPos i, hslackGap i]
    have hradiusLoss : 2 * radius (left i) < 2 * coreTolerance := by
      linarith [hradiusSmall (left i)]
    have heq : cellUpper i - cellLower i - 8 * epsilon i =
        innerUpper i - innerLower i - 2 * radius (left i) - 3 * slack i / 4 := by
      dsimp [cellUpper, cellLower, upper0, lower0, margin, epsilon, left]
      ring_nf
    rw [heq]
    dsimp [widthGap] at hthree
    linarith [hradiusLoss]
  have heffectivePos (i : cellIndex) : 0 < effectiveHalfWidth i := by
    dsimp [effectiveHalfWidth]
    linarith [heffectiveWidth i, htarget i]
  have htargetHalfPos (i : cellIndex) : 0 < targetWidth i / 2 :=
    div_pos (htarget i) (by norm_num)
  have hhalfWidth (i : cellIndex) : targetWidth i / 2 < effectiveHalfWidth i := by
    dsimp [effectiveHalfWidth]
    linarith [heffectiveWidth i]
  have htargetPowPos (i : cellIndex) : 0 < (targetWidth i / 2) ^ α :=
    Real.rpow_pos_of_pos (htargetHalfPos i) α
  have heffectivePowPos (i : cellIndex) : 0 < (effectiveHalfWidth i) ^ α :=
    Real.rpow_pos_of_pos (heffectivePos i) α
  have hpowStrict (i : cellIndex) :
      (targetWidth i / 2) ^ α < (effectiveHalfWidth i) ^ α :=
    Real.rpow_lt_rpow (le_of_lt (htargetHalfPos i)) (hhalfWidth i) hα
  have hcoefficientStrict (i : cellIndex) :
      C / (targetWidth i / 2) ^ α < C / (effectiveHalfWidth i) ^ α := by
    apply (div_lt_div_iff₀ (htargetPowPos i) (heffectivePowPos i)).2
    exact mul_lt_mul_of_neg_left (hpowStrict i) hEscape.negative
  let delta (i : cellIndex) : ℝ :=
    (C / (effectiveHalfWidth i ^ α) - C / ((targetWidth i / 2) ^ α)) / 2
  have hdelta : ∀ i : cellIndex, 0 < delta i := by
    intro i
    dsimp [delta]
    exact div_pos (sub_pos.mpr (hcoefficientStrict i)) (by norm_num)
  have hcoefficient (i : cellIndex) :
      C / ((targetWidth i / 2) ^ α) ≤
        C / (effectiveHalfWidth i ^ α) - delta i := by
    dsimp [delta]
    linarith [hcoefficientStrict i]
  have hendpointBand' : ∀ i : cellIndex,
      3 * epsilon i <
        (radius (right i) - radius (left i)) / 2 := by
    simpa [radiusIncrease, left, right] using hendpointBand
  have hbridgeWindows' : ∀ i : cellIndex,
      cellLower i + 4 * epsilon i <
          center (right i) - center (left i) - 4 * epsilon i ∧
        center (right i) - center (left i) + 4 * epsilon i <
          cellUpper i - 4 * epsilon i := by
    simpa [displacement, left, right] using hbridgeWindows
  obtain ⟨amplitude, hamplitude, hproduct⟩ :=
    exists_eventually_iidSequenceLaw_normalizedStepCorridor_lowerBound_of_endpointCoreBridges
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase upper lower center radius
      innerLower innerUpper hcenter0' hradius0' hradiusStep hcores hgeometry
      cellLower cellUpper epsilon margin delta hlower hupper hmargin hepsilon hdelta
      hendpointBand' hreturnWindows hbridgeWindows'
  let total (i : cellIndex) (n : ℕ) :=
    commonPartitionCellStepLength n upper lower i
  let coreCount (i : cellIndex) (n : ℕ) :=
    Asymptotics.balancedBlockCount
      (total i n - stableBlockLength α ν (amplitude i ^ α) scale n)
      (stableBlockLength α ν (amplitude i ^ α) scale n) + 1
  let exponent (i : cellIndex) : ℝ :=
    (C / (effectiveHalfWidth i ^ α) - delta i) * amplitude i ^ α
  let probability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower}
  have hproduct' : ∀ᶠ n : ℕ in atTop,
      (∏ i : cellIndex, ENNReal.ofReal (Real.exp (exponent i)) ^ coreCount i n) ≤
        probability n := by
    filter_upwards [hproduct] with n hn
    simpa [probability, exponent, effectiveHalfWidth, coreCount, total] using hn
  have htotal (i : cellIndex) :
      Tendsto (fun n => (total i n : ℝ) / (n : ℝ)) atTop (nhds (duration i)) := by
    simpa [total, duration] using
      tendsto_commonPartitionCellStepLength_div_nat upper lower i
  have hcountRate (i : cellIndex) : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n * (coreCount i n : ℝ))
      atTop (nhds (duration i / amplitude i ^ α)) := by
    exact tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount
      hα hα₂ (hamplitude i) hscale hslow (hduration i) (total i) (htotal i)
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
  have hprobabilityLeOne (n : ℕ) : probability n ≤ 1 := by
    calc
      probability n ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hfiniteProduct := eventually_probabilityRate_ge_finiteProductRate
    exponent coreCount (fun i => duration i / amplitude i ^ α) hcountRate
    hproduct' hrateNonneg hprobabilityLeOne herror
  let targetTerm (i : cellIndex) : ℝ :=
    C * duration i / ((targetWidth i / 2) ^ α)
  have htermBound (i : cellIndex) :
      targetTerm i ≤ (duration i / amplitude i ^ α) * exponent i := by
    have hamplitudePos : 0 < amplitude i ^ α :=
      Real.rpow_pos_of_pos (hamplitude i) α
    have hexponentEq :
        (duration i / amplitude i ^ α) * exponent i =
          duration i * (C / (effectiveHalfWidth i ^ α) - delta i) := by
      dsimp [exponent]
      field_simp [ne_of_gt hamplitudePos]
    calc
      targetTerm i = duration i * (C / ((targetWidth i / 2) ^ α)) := by
        dsimp [targetTerm]
        ring
      _ ≤ duration i * (C / (effectiveHalfWidth i ^ α) - delta i) :=
        mul_le_mul_of_nonneg_left (hcoefficient i) (le_of_lt (hduration i))
      _ = (duration i / amplitude i ^ α) * exponent i := hexponentEq.symm
  have hlimitLower :
      (∑ i : cellIndex, targetTerm i) ≤
        ∑ i : cellIndex, (duration i / amplitude i ^ α) * exponent i :=
    Finset.sum_le_sum fun i _ => htermBound i
  have htargetRateEq :
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          ((targetWidth i / 2) ^ α)) =
        ∑ i : cellIndex, targetTerm i := by
    rfl
  filter_upwards [hfiniteProduct] with n hn
  rcases hn with ⟨hprobabilityPos, hbound⟩
  refine ⟨?_, ?_⟩
  · simpa [probability] using hprobabilityPos
  · have htargetBound :
        (∑ i : cellIndex, targetTerm i) - error ≤
          stableSmallDeviationRate α ν scale n * Real.log (probability n).toReal := by
      linarith [hlimitLower, hbound]
    simpa [probability, htargetRateEq] using htargetBound


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
