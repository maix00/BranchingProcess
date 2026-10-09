/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.Support.Corridor
public import Probability.Process.Path.Skorokhod.Corridor.Segment

/-!
# Transfer support of a path law to process corridor events

The support criteria for arbitrary càdlàg path laws live in `MeasureTheory`.
This file transfers them through a measurable path-valued version of a
stochastic process.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

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
    simp only [Set.mem_preimage, fullSegmentCorridorReturnEvent]
    constructor
    · rintro ⟨⟨margin, hmargin, hcorridor⟩, hendω⟩
      exact ⟨⟨margin, hmargin, fun t => by simpa [hω t] using hcorridor t⟩,
        by simpa [hω ⊤] using hendω⟩
    · rintro ⟨⟨margin, hmargin, hcorridor⟩, hendω⟩
      exact ⟨⟨margin, hmargin, fun t => by simpa [hω t] using hcorridor t⟩,
        by simpa [hω ⊤] using hendω⟩
  have hpos : 0 < (P.map F) A :=
    MeasureTheory.CadlagPath.measure_skorokhodCorridorEndsIn_pos_of_straightPath_mem_support
      (P.map F) hzero hy hend hsupport
  rwa [Measure.map_apply hF hA, measure_congr heq] at hpos

end ProbabilityTheory

end
