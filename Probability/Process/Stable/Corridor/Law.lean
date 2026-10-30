/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Corridor.Range
public import Probability.Process.Stable.Levy
import Order.Interval.RationalCoordinate.UnitInterval
import Probability.Process.Stable.FiniteDimensional

/-!
# Law invariance of stable corridor events

## Public declarations

- If two stable Lévy processes have the same index and increment law, their
  rational range-tube probabilities agree at every width:
  $P_X(\mathrm{tube}(a))=P_Y(\mathrm{tube}(a))$.

The rational event-law transfer itself is stated in the generic corridor
module. This result supplies the rational-time process law from the stable
increment specification.
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
  let clock : RationalCoordinate.UnitInterval → ℝ :=
    fun q => (RationalCoordinate.toNNReal q : ℝ)
  have hXclock : HasStableClockIncrements α μ clock
      (fun q ω => X (RationalCoordinate.toNNReal q) ω) P := by
    exact hX.increments.comp_time RationalCoordinate.toNNReal RationalCoordinate.monotone_toNNReal
      RationalCoordinate.toNNReal_bot
  have hYclock : HasStableClockIncrements α μ clock
      (fun q ω => Y (RationalCoordinate.toNNReal q) ω) Q := by
    exact hY.increments.comp_time RationalCoordinate.toNNReal RationalCoordinate.monotone_toNNReal
      RationalCoordinate.toNNReal_bot
  have hlaw := hXclock.process_identDistrib_of_aemeasurable hYclock
    (AEMeasurable.of_eval fun q => hXclock.aemeasurable_eval q)
    (AEMeasurable.of_eval fun q => hYclock.aemeasurable_eval q)
  exact rationalRangeProbability_eq_of_rationalProcess_identDistrib hlaw a

end ProbabilityTheory

end
