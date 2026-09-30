module

public import Mathlib.MeasureTheory.Measure.Support
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Positive corridor probability from path support

The measure-theoretic support criterion is supplied by Mathlib. Only the
specific straight-path witness for an endpoint-constrained corridor is
provided here.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- If the straight path to an admissible endpoint belongs to the support
of a càdlàg path law, then the corresponding open corridor has positive
probability. -/
theorem measure_skorokhodCorridorEndsIn_pos_of_straightPath_mem_support
    (Q : Measure (CadlagPath unitInterval ℝ))
    {lower upper endpointLower endpointUpper y : ℝ}
    (hzero : lower < 0 ∧ 0 < upper)
    (hy : lower < y ∧ y < upper)
    (hend : endpointLower < y ∧ y < endpointUpper)
    (hsupport : Skorokhod.straightPath y ∈ Q.support) :
    0 < Q (Skorokhod.rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  have hmem := Skorokhod.straightPath_mem_rangeInOpenIntervalEndsIn
    hzero hy hend
  exact (Measure.mem_support_iff_forall _).mp hsupport _
    ((Skorokhod.isOpen_rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper).mem_nhds hmem)

end ProbabilityTheory

end
