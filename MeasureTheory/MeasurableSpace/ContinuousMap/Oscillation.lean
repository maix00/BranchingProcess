/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Topology.ContinuousMap.Oscillation

/-!
# Measurability of continuous-path oscillation sets

-/

@[expose] public section

namespace ContinuousMap

/-- Measurability of the range-diameter constraint on continuous paths. -/
theorem measurableSet_rangeOscillationSet
    [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]
    (width : ℝ) : MeasurableSet (rangeOscillationSet width) :=
  (isClosed_rangeOscillationSet width).measurableSet

/-- Measurability of the set of paths starting at zero. -/
theorem measurableSet_startsAtZeroSet
    [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)] :
    MeasurableSet startsAtZeroSet := isClosed_startsAtZeroSet.measurableSet

end ContinuousMap

end
