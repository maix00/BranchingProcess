/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Feedback
public import Probability.Process.Path.Skorokhod.Corridor.Segment
import Topology.Order.UnitInterval.Rational

/-!
# Complete-path bound from successful feedback blocks

The finite block event is first controlled at rational times. Càdlàg
regularity then transfers a closed bound to the complete unit interval.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- A successful finite feedback path stays uniformly close to its target
line on the entire unit interval. The factor two leaves room for a direct
dense-coordinate bound and is harmless when selecting the block tolerance. -/
theorem rationalFeedback_fullPath_bound
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hcadlag : IsCadlag (fun t => X t ω))
    {blocks : ℕ} (hblocks : 0 < blocks)
    (v δ r R η : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hη : 2 * (R + δ + |v / (blocks : ℝ)|) < η)
    (hsuccess : rationalUniformPrefixPath X blocks blocks hblocks ω ∈
      rationalFeedbackPrefixSet hblocks blocks
        (fun j => v * (j.val : ℝ) / (blocks : ℝ))
        (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
        (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r))) :
    ∀ t : unitInterval,
      |X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)| < η := by
  let f : ↑RationalCoordinate.UnitInterval → ℝ :=
    fun q => X (RationalCoordinate.toNNReal q) ω - X 0 ω
  have hf0 : f ⊥ = 0 := by simp [f, RationalCoordinate.toNNReal_bot]
  have hsuccess' : f ∈ rationalFeedbackPrefixSet hblocks blocks
      (fun j => v * (j.val : ℝ) / (blocks : ℝ))
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) r R)
      (feedbackCorrectionSet δ (v / (blocks : ℝ)) (-R) (-r)) :=
    (mem_rationalFeedbackPrefixSet_prefix_iff X hblocks blocks ω
      _ _ _).mp hsuccess
  let Z : unitInterval → ℝ := fun t =>
    X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)
  have hZ : IsCadlag Z := by
    have hsegment := isCadlag_segmentIncrement X 0 1 ω hcadlag
    have hlinear : Continuous (fun t : unitInterval => v * (t : ℝ)) :=
      continuous_const.mul continuous_subtype_val
    convert hsegment.sub hlinear.isCadlag using 1
    funext t
    change X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ) =
      X (0 + 1 * UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)
    simp only [zero_add, one_mul]
  have hrat (q : ↑RationalCoordinate.UnitInterval) :
      |Z (RationalCoordinate.toUnitInterval q)| ≤
        R + δ + |v / (blocks : ℝ)| := by
    simpa [Z, f, RationalCoordinate.toNNReal, UnitInterval.toNNReal,
      RationalCoordinate.toUnitInterval] using
        rationalFeedback_coordinate_bound hblocks f hf0 v δ r R
          hr hR hsuccess' q
  have hD : Dense (Set.range RationalCoordinate.toUnitInterval) :=
    RationalCoordinate.denseRange_toUnitInterval
  have htop : (⊤ : unitInterval) ∈ Set.range RationalCoordinate.toUnitInterval := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [RationalCoordinate.toUnitInterval]
  have hpair : ∀ s ∈ Set.range RationalCoordinate.toUnitInterval,
      ∀ t ∈ Set.range RationalCoordinate.toUnitInterval,
      |Z s - Z t| ≤ 2 * (R + δ + |v / (blocks : ℝ)|) := by
    rintro s ⟨qs, rfl⟩ t ⟨qt, rfl⟩
    have hs := hrat qs
    have ht := hrat qt
    have htri := abs_sub_le (Z (RationalCoordinate.toUnitInterval qs)) 0
      (Z (RationalCoordinate.toUnitInterval qt))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    linarith
  have hall := Skorokhod.oscillationBounded_on_dense hD htop Z hZ hpair
  have hZ0 : Z ⊥ = 0 := by
    change X 0 ω - X 0 ω - v * 0 = 0
    ring
  intro t
  have hbound := hall t ⊥
  simpa only [hZ0, sub_zero] using lt_of_le_of_lt hbound hη

end ProbabilityTheory

end
