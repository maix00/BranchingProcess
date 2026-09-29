import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.Corridor
import Topology.Cadlag.Skorokhod.Endpoint

/-!
# Open Skorokhod corridors with an endpoint constraint

The event combines a uniformly interior path corridor with an open condition
on the terminal value.  Both conditions are open in the `J₁` topology.
-/

open Set

namespace Skorokhod

/-- Paths that remain uniformly inside an open interval and whose terminal
value belongs to a prescribed open interval. -/
def rangeInOpenIntervalEndsIn (lower upper endpointLower endpointUpper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  rangeInOpenInterval lower upper ∩
    (fun path : CadlagPath unitInterval ℝ => path ⊤) ⁻¹'
      Set.Ioo endpointLower endpointUpper

theorem mem_rangeInOpenIntervalEndsIn_iff
    {lower upper endpointLower endpointUpper : ℝ}
    {path : CadlagPath unitInterval ℝ} :
    path ∈ rangeInOpenIntervalEndsIn lower upper endpointLower endpointUpper ↔
      path ∈ rangeInOpenInterval lower upper ∧
        path ⊤ ∈ Set.Ioo endpointLower endpointUpper :=
  Iff.rfl

theorem isOpen_rangeInOpenIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    IsOpen (rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  exact (isOpen_rangeInOpenInterval lower upper).inter
    (isOpen_Ioo.preimage continuous_apply_top)

theorem measurableSet_rangeInOpenIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    MeasurableSet (rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) :=
  (isOpen_rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper).measurableSet

/-- Paths that remain in a closed interval and whose terminal value lies in
a prescribed closed interval. -/
def rangeInClosedIntervalEndsIn (lower upper endpointLower endpointUpper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  rangeInClosedInterval lower upper ∩
    (fun path : CadlagPath unitInterval ℝ => path ⊤) ⁻¹'
      Set.Icc endpointLower endpointUpper

theorem mem_rangeInClosedIntervalEndsIn_iff
    {lower upper endpointLower endpointUpper : ℝ}
    {path : CadlagPath unitInterval ℝ} :
    path ∈ rangeInClosedIntervalEndsIn lower upper endpointLower endpointUpper ↔
      path ∈ rangeInClosedInterval lower upper ∧
        path ⊤ ∈ Set.Icc endpointLower endpointUpper :=
  Iff.rfl

theorem isClosed_rangeInClosedIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    IsClosed (rangeInClosedIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  exact (isClosed_rangeInClosedInterval lower upper).inter
    (isClosed_Icc.preimage continuous_apply_top)

theorem measurableSet_rangeInClosedIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    MeasurableSet (rangeInClosedIntervalEndsIn
      lower upper endpointLower endpointUpper) :=
  (isClosed_rangeInClosedIntervalEndsIn
    lower upper endpointLower endpointUpper).measurableSet

end Skorokhod
