/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.NullMeasurable
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw
import Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor

/-!
# Stable small-deviation rate for constant `M₂` corridors

The source's pointwise-strict corridor need not be open in `J₁`: a càdlàg
path can approach a boundary through a left limit without attaining it.  For
constant finite boundaries, its stable small-width rate can nevertheless be
obtained by squeezing the exact event between narrower and wider uniformly
interior corridors.  This avoids a boundary-null hypothesis and preserves
the pointwise event.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The exact pointwise-strict corridor between finite constant boundaries,
with the source's pinned-zero starting condition. -/
def constantCorridorEvent (lower upper : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0 ∧ ∀ t, lower < f t ∧ f t < upper}

theorem corridorSet_constant_eq (lower upper : ℝ) :
    corridorSet (StepBoundary.constant (upper : EReal))
      (StepBoundary.constant (lower : EReal)) = constantCorridorEvent lower upper := by
  ext f
  simp [corridorSet, constantCorridorEvent, StepBoundary.eval_constant]

/-- The constant corridor is an `M₂` corridor whenever it contains the
origin.  The constant zero path witnesses continuous admissibility. -/
def M2Corridor.constantBounds {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) : M2Corridor where
  upper := StepBoundary.constant (upper : EReal)
  lower := StepBoundary.constant (lower : EReal)
  hasContinuousAdmissiblePath := by
    let f : C(unitInterval, ℝ) := ContinuousMap.const unitInterval 0
    refine ⟨f, rfl, ?_⟩
    rw [corridorSet_constant_eq]
    constructor
    · rfl
    · intro t
      simp only [f, ContinuousMap.const_apply, Skorokhod.ofContinuousMap_apply]
      exact ⟨hlower, hupper⟩

@[simp]
theorem M2Corridor.constantBounds_toSet {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) :
    (M2Corridor.constantBounds hlower hupper).toSet =
      constantCorridorEvent lower upper := by
  simp [M2Corridor.toSet, M1Corridor.toSet, M2Corridor.constantBounds,
    corridorSet_constant_eq]

/-- The exact event obtained by shrinking a fixed constant corridor by the
positive factor `a`. -/
def scaledConstantCorridorEvent (a lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  constantCorridorEvent (a * lower) (a * upper)

theorem scaledConstantCorridorEvent_eq_toSet
    {a lower upper : ℝ} (ha : 0 < a) (hlower : lower < 0) (hupper : 0 < upper) :
    scaledConstantCorridorEvent a lower upper =
      (M2Corridor.constantBounds (mul_neg_of_pos_of_neg ha hlower)
        (mul_pos ha hupper)).toSet := by
  simp [scaledConstantCorridorEvent, M2Corridor.constantBounds_toSet]

/-- Uniformly interior path corridors transfer to the corresponding process
complete-segment event under matching stable increment laws. -/
private theorem measure_rangeInOpenInterval_eq_fullSegmentCorridorEvent
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q) (lower upper : ℝ) :
    P (Skorokhod.rangeInOpenInterval lower upper) =
      Q (fullSegmentCorridorEvent X 0 1 lower upper) := by
  have hpath : Skorokhod.rangeInOpenIntervalEndsIn lower upper
      (lower - 1) (upper + 1) = Skorokhod.rangeInOpenInterval lower upper := by
    ext f
    simp only [Skorokhod.rangeInOpenIntervalEndsIn, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨margin, hmargin, hvalues⟩, hend⟩
      exact ⟨margin, hmargin, hvalues⟩
    · rintro ⟨margin, hmargin, hvalues⟩
      refine ⟨⟨margin, hmargin, hvalues⟩, ?_⟩
      have ht := hvalues ⊤
      constructor <;> linarith
  have hproc : fullSegmentCorridorReturnEvent X 0 1 lower upper
      (lower - 1) (upper + 1) = fullSegmentCorridorEvent X 0 1 lower upper := by
    ext ω
    simp only [fullSegmentCorridorReturnEvent, segmentCorridorEndpointEvent,
      Set.mem_inter_iff, Set.mem_ofPred_eq, fullSegmentCorridorEvent]
    constructor
    · rintro ⟨hpath, _⟩
      exact hpath
    · intro hpath
      refine ⟨hpath, ?_⟩
      obtain ⟨margin, hmargin, hvalues⟩ := hpath
      have ht := hvalues ⊤
      change segmentIncrement X 0 1 ω ⊤ ∈ Set.Ioo (lower - 1) (upper + 1)
      simp only [Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
  calc
    P (Skorokhod.rangeInOpenInterval lower upper) =
        P (Skorokhod.rangeInOpenIntervalEndsIn lower upper
          (lower - 1) (upper + 1)) := by rw [hpath]
    _ = Q (fullSegmentCorridorReturnEvent X 0 1 lower upper
          (lower - 1) (upper + 1)) :=
        hP.measure_corridorReturnEvent_eq hX lower upper (lower - 1) (upper + 1)
    _ = Q (fullSegmentCorridorEvent X 0 1 lower upper) := by rw [hproc]

/-! The exact event is between a smaller open corridor and a slightly
expanded open corridor. -/

private theorem rangeInOpenInterval_subset_pointwiseCorridor
    {lo hi lower upper : ℝ}
    (hlo : lo < lower) (hhi : upper < hi) :
    Skorokhod.rangeInOpenInterval lower upper ⊆
      {f : CadlagPath unitInterval ℝ | ∀ t, lo < f t ∧ f t < hi} := by
  intro f hf
  obtain ⟨margin, hmargin, hpath⟩ := hf
  intro t
  refine ⟨?_, ?_⟩
  · obtain ⟨hlo', _⟩ := hpath t
    linarith
  · obtain ⟨_, hhi'⟩ := hpath t
    linarith

private theorem constantCorridorEvent_subset_rangeInOpenInterval
    {lower upper lo hi : ℝ}
    (hlo : lo < lower) (hhi : upper < hi) :
    constantCorridorEvent lower upper ⊆
      Skorokhod.rangeInOpenInterval lo hi := by
  intro f hf
  rcases hf with ⟨_, hpath⟩
  let margin : ℝ := min (lower - lo) (hi - upper) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact half_pos (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi))
  refine ⟨margin, hmargin, fun t => ?_⟩
  obtain ⟨hl, hu⟩ := hpath t
  constructor <;> dsimp [margin] <;> have hm := min_le_left (lower - lo) (hi - upper) <;>
    have hm' := min_le_right (lower - lo) (hi - upper) <;> linarith

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
