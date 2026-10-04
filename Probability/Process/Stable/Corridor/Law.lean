/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Corridor.Range
public import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Path.Skorokhod.RationalTime
public import Probability.Process.Stable.SmallDeviation.RationalTube

/-!
# Law invariance of stable corridor events

Rational range-tube probabilities depend only on the stable increment law.
This process-level result does not require an escape-rate limit.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal Topology

/-- Stable Lévy processes with the same index and one-step law have the same
rational range-tube probabilities at every width. -/
theorem IsStableLevyProcess.rationalRangeProbability_eq_of_same_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X P)
    (hY : IsStableLevyProcess α μ Y Q) (a : ℝ) :
    rationalRangeProbability P X a = rationalRangeProbability Q Y a := by
  let clock : RationalGrid.RationalUnitInterval → ℝ :=
    fun q => (rationalUnitTime q : ℝ)
  have hXclock : HasStableClockIncrements α μ clock
      (fun q ω => X (rationalUnitTime q) ω) P := by
    exact hX.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hYclock : HasStableClockIncrements α μ clock
      (fun q ω => Y (rationalUnitTime q) ω) Q := by
    exact hY.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hlaw := hXclock.process_identDistrib_of_aemeasurable hYclock
    (AEMeasurable.of_eval fun q => hXclock.aemeasurable_eval q)
    (AEMeasurable.of_eval fun q => hYclock.aemeasurable_eval q)
  have hprob := hlaw.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube (2 * a))
  have hprob' : P (rationalHorizonTubeEvent X 1 (2 * a)) =
      Q (rationalHorizonTubeEvent Y 1 (2 * a)) := by
    change P ((fun ω q => X (1 * rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a)) =
      Q ((fun ω q => Y (1 * rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a))
    simpa only [one_mul] using hprob
  simpa [rationalRangeProbability] using hprob'

end ProbabilityTheory

end
