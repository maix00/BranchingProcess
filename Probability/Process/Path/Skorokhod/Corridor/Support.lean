module

public import Mathlib.MeasureTheory.Measure.Support
public import Probability.Process.Path.Skorokhod.Corridor.Segment
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
open scoped NNReal

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

/-- Transfer the path-support criterion to the full segment event of a
process. The path-valued representative need only agree almost surely with
the complete centered segment. -/
theorem measure_fullSegmentCorridorReturnEvent_pos_of_path_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (F : Ω → CadlagPath unitInterval ℝ) (hF : Measurable F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : unitInterval,
      F ω t = segmentIncrement X 0 1 ω t)
    {lower upper endpointLower endpointUpper y : ℝ}
    (hzero : lower < 0 ∧ 0 < upper)
    (hy : lower < y ∧ y < upper)
    (hend : endpointLower < y ∧ y < endpointUpper)
    (hsupport : Skorokhod.straightPath y ∈ (P.map F).support) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      lower upper endpointLower endpointUpper) := by
  let A := Skorokhod.rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper
  have hA : MeasurableSet A :=
    Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper
  have heq : F ⁻¹' A =ᵐ[P] fullSegmentCorridorReturnEvent X 0 1
      lower upper endpointLower endpointUpper := by
    filter_upwards [hpath] with ω hω
    apply propext
    simp only [Set.mem_preimage,
      fullSegmentCorridorReturnEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨margin, hmargin, hcorridor⟩, hendω⟩
      exact ⟨⟨margin, hmargin, fun t => by simpa [hω t] using hcorridor t⟩,
        by simpa [hω ⊤] using hendω⟩
    · rintro ⟨⟨margin, hmargin, hcorridor⟩, hendω⟩
      exact ⟨⟨margin, hmargin, fun t => by simpa [hω t] using hcorridor t⟩,
        by simpa [hω ⊤] using hendω⟩
  have hpos : 0 < (P.map F) A :=
    measure_skorokhodCorridorEndsIn_pos_of_straightPath_mem_support
      (P.map F) hzero hy hend hsupport
  rwa [Measure.map_apply hF hA, measure_congr heq] at hpos

end ProbabilityTheory

end
