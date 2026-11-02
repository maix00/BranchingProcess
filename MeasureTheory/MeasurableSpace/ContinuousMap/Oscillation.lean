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

## Public declarations

The measurable path sets are the range-diameter constraint and the initial
value constraint:

\[
\operatorname{rangeOscillationSet}(w)
=\{f:\forall s,t\in[0,1],\ |f(s)-f(t)|\le w\},
\qquad
\operatorname{startsAtZeroSet}=\{f:f(0)=0\}.
\]

* `ContinuousMap.measurableSet_rangeOscillationSet`: the set of paths with
  range diameter at most `width` is measurable.
* `ContinuousMap.measurableSet_startsAtZeroSet`: the paths whose value at
  time zero is zero form a measurable set.

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
