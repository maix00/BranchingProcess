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

end Skorokhod
