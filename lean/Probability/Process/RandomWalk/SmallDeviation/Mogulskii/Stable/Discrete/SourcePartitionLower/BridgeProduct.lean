/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SourcePartitionLowerProbability
import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.LowerGeometry
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableLower.CellBridge
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

/-!
# Endpoint-core block bounds and finite-cell product gluing.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod.PathClass.StepCorridor
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- The endpoint-core construction gives eventual positivity of a finite
step-corridor probability. Its hypotheses expose the cell geometry and the
small positive margins needed by the stable open-corridor block estimate. -/
theorem exists_eventually_iidSequenceLaw_sourceNormalizedStepCorridor_lowerBound_of_endpointCoreBridges
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
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : ∀ j, j.val = 0 → center j = 0)
    (hradius0 : ∀ j, j.val = 0 → radius j = 0)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
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
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    (cellLower cellUpper epsilon margin delta :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i,
      cellLower i = innerLower i +
        radius (commonPartitionCellLeftKnotIndex upper lower i) + margin i -
        center (commonPartitionCellLeftKnotIndex upper lower i))
    (hupper : ∀ i,
      cellUpper i = innerUpper i -
        radius (commonPartitionCellLeftKnotIndex upper lower i) - margin i -
        center (commonPartitionCellLeftKnotIndex upper lower i))
    (hmargin : ∀ i, 0 < margin i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hdelta : ∀ i, 0 < delta i)
    (hendpointBand : ∀ i,
      3 * epsilon i <
        (radius (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2)
    (hreturnWindows : ∀ i, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
      cellLower i + 4 * epsilon i < (((j : ℝ) - 1) * epsilon i) ∧
        ((j : ℝ) + 1) * epsilon i < cellUpper i - 4 * epsilon i)
    (hbridgeWindows : ∀ i,
      cellLower i + 4 * epsilon i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            center (commonPartitionCellLeftKnotIndex upper lower i) - 4 * epsilon i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) -
            center (commonPartitionCellLeftKnotIndex upper lower i) + 4 * epsilon i <
          cellUpper i - 4 * epsilon i) :
    ∃ amplitude : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ,
      (∀ i, 0 < amplitude i) ∧
      ∀ᶠ n : ℕ in atTop,
        (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          ENNReal.ofReal (Real.exp
            ((C / (((cellUpper i - cellLower i - 8 * epsilon i) / 2) ^ α) -
              delta i) * amplitude i ^ α)) ^
              (Asymptotics.balancedBlockCount
                (sourcePartitionCellStepLengths n upper lower i.val -
                  stableBlockLength α ν (amplitude i ^ α) scale n)
                (stableBlockLength α ν (amplitude i ^ α) scale n) + 1)) ≤
          iidSequenceLaw ν {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
  let cellIndex := Fin ((StepBoundary.commonKnots upper lower).card - 1)
  let duration : cellIndex → ℝ := fun i =>
    (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ) -
      StepBoundary.commonPartitionGrid upper lower i.val
  let total : cellIndex → ℕ → ℕ := fun i n =>
    sourcePartitionCellStepLengths n upper lower i.val
  have hcellExists (i : cellIndex) : ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / (((cellUpper i - cellLower i - 8 * epsilon i) / 2) ^ α) - delta i) *
          a ^ α)) ^
          (Asymptotics.balancedBlockCount
            (total i n - stableBlockLength α ν (a ^ α) scale n)
            (stableBlockLength α ν (a ^ α) scale n) + 1) ≤
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 (total i n) increment ∈
              {block | partitionCellCoreReturnBlockEvent
                (scale n * innerLower i) (scale n * innerUpper i)
                (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}} := by
    have hduration : 0 < duration i := by
      dsimp [duration]
      have h := StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
      exact sub_pos.mpr (by exact_mod_cast h)
    have htotal : Tendsto (fun n => (total i n : ℝ) / (n : ℝ))
        atTop (nhds (duration i)) := by
      simpa [total, duration] using
        tendsto_sourcePartitionCellStepLength_div_nat upper lower i
    exact exists_eventually_partitionCellCoreReturnBlockEvent_ge_exp_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      (by rw [hlower i]) (by rw [hupper i]) (hmargin i) (hepsilon i) (hdelta i)
      (hendpointBand i) (hreturnWindows i) (hbridgeWindows i)
      (total i) hduration htotal
  let amplitude : cellIndex → ℝ := fun i => Classical.choose (hcellExists i)
  have hamplitude : ∀ i : cellIndex, 0 < amplitude i := by
    intro i
    exact (Classical.choose_spec (hcellExists i)).1
  let cellBound : cellIndex → ℕ → ENNReal := fun i n =>
    ENNReal.ofReal (Real.exp
      ((C / (((cellUpper i - cellLower i - 8 * epsilon i) / 2) ^ α) - delta i) *
        amplitude i ^ α)) ^
      (Asymptotics.balancedBlockCount
        (total i n - stableBlockLength α ν (amplitude i ^ α) scale n)
        (stableBlockLength α ν (amplitude i ^ α) scale n) + 1)
  have hlocal : ∀ i : cellIndex, ∀ᶠ n : ℕ in atTop,
      cellBound i n ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (total i n) increment ∈
            {block | partitionCellCoreReturnBlockEvent
              (scale n * innerLower i) (scale n * innerUpper i)
              (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
              (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
              (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
              (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}} := by
    intro i
    have hdata := (Classical.choose_spec (hcellExists i)).2
    simpa [cellBound, amplitude, total] using hdata
  have hproduct :=
    eventually_iidSequenceLaw_sourceNormalizedStepCorridor_ge_prod_of_partitionCellCoreReturnBounds
      ν hscale.eventually_scale_pos upper lower center radius innerLower innerUpper
      hcenter0 hradius0 hradiusStep hcores (fun i => ⟨
        (hgeometry i).1,
        (hgeometry i).2.2.2.2.2⟩) cellBound (by
          intro i
          have hlength (n : ℕ) :
              sourcePartitionCellStepLengths n upper lower i.val = total i n := by
            simp [total, commonPartitionCellStepLengths,
              commonPartitionCellStepLength, commonPartitionFloorTimeIndex, i.isLt]
          filter_upwards [hlocal i] with n hn
          rw [hlength n]
          exact hn)
  refine ⟨amplitude, hamplitude, ?_⟩
  simpa [cellBound, amplitude, total] using hproduct


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
