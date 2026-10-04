/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FullCorridor
public import Probability.Process.Path.Skorokhod.Corridor.Support

/-!
# Support of the stable path law

Path-support consequences of positive complete-path corridor probabilities.
The corridor estimates themselves live in `Lower.FullCorridor` and do not
depend on the Skorokhod support API.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The complete centered-corridor estimates place the zero path in the
support of a measurable càdlàg representative of the unit segment. -/
theorem IsStableLevyProcess.straightPath_zero_mem_segmentLaw_support
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (F : Ω → CadlagPath unitInterval ℝ) (hF : Measurable F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : unitInterval,
      F ω t = segmentIncrement X 0 1 ω t)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    Skorokhod.straightPath 0 ∈ (P.map F).support := by
  apply straightPath_zero_mem_support_of_centeredCorridors_pos
  intro δ hδ
  have hcorridor : 0 < P (fullSegmentCorridorEvent X 0 1 (-δ) δ) :=
    h.measure_fullSegmentCorridor_pos (-δ) δ (by linarith) hδ hpos hneg
  have heq : F ⁻¹' Skorokhod.rangeInOpenInterval (-δ) δ =ᵐ[P]
      fullSegmentCorridorEvent X 0 1 (-δ) δ := by
    filter_upwards [hpath] with ω hω
    apply propext
    simp only [Set.mem_preimage, Skorokhod.rangeInOpenInterval,
      fullSegmentCorridorEvent, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨margin, hmargin, hbound⟩
      exact ⟨margin, hmargin, fun t => by simpa [hω t] using hbound t⟩
    · rintro ⟨margin, hmargin, hbound⟩
      exact ⟨margin, hmargin, fun t => by simpa [hω t] using hbound t⟩
  rw [Measure.map_apply hF
    (Skorokhod.measurableSet_rangeInOpenInterval (-δ) δ), measure_congr heq]
  exact hcorridor

end ProbabilityTheory

end
