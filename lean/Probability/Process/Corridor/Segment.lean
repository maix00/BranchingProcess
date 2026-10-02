module

public import Probability.Process.Path.UnitInterval
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Complete corridor events on a time segment

This module defines pathwise segment increments and corridor events without
using a path-space topology. Endpoint conventions are represented by an
arbitrary measurable-set parameter; the `Ioo` and `Ioc` events used by
applications are special cases.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- A segment of a process, translated to start at zero. -/
def segmentIncrement {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (ω : Ω) (t : unitInterval) : ℝ :=
  X (start + length * unitIntervalToNNReal t) ω - X start ω

/-- The complete segment remains a positive uniform distance inside a
spatial corridor. -/
def fullSegmentCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) : Set Ω :=
  {ω | ∃ margin > 0, ∀ t : unitInterval,
    lower + margin ≤ segmentIncrement X start length ω t ∧
      segmentIncrement X start length ω t ≤ upper - margin}

/-- A complete-segment corridor constrains its terminal increment to the
corresponding closed interval. -/
theorem fullSegmentCorridorEvent_subset_endpoint_Icc
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) :
    fullSegmentCorridorEvent X start length lower upper ⊆
      {ω | segmentIncrement X start length ω ⊤ ∈ Set.Icc lower upper} := by
  rintro ω ⟨margin, hmargin, hpath⟩
  have hend := hpath ⊤
  exact ⟨by linarith, by linarith⟩

/-- A corridor event with an arbitrary endpoint constraint. -/
def segmentCorridorEndpointEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) (J : Set ℝ) : Set Ω :=
  fullSegmentCorridorEvent X start length lower upper ∩
    {ω | segmentIncrement X start length ω ⊤ ∈ J}

/-- The endpoint-constrained complete segment corridor with an open window. -/
def fullSegmentCorridorReturnEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) : Set Ω :=
  segmentCorridorEndpointEvent X start length lower upper
    (Set.Ioo coreLower coreUpper)

/-- The endpoint-constrained complete segment corridor with a
left-open, right-closed window. -/
def fullSegmentCorridorIocReturnEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) : Set Ω :=
  segmentCorridorEndpointEvent X start length lower upper
    (Set.Ioc coreLower coreUpper)

/-- Enlarging a spatial corridor and its arbitrary endpoint set preserves
the corresponding event. -/
theorem segmentCorridorEndpointEvent_mono
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ lower₂ upper₂ : ℝ} {J₁ J₂ : Set ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hJ : J₁ ⊆ J₂) :
    segmentCorridorEndpointEvent X start length lower₁ upper₁ J₁ ⊆
      segmentCorridorEndpointEvent X start length lower₂ upper₂ J₂ := by
  rintro ω ⟨⟨margin, hmargin, hpath⟩, hend⟩
  refine ⟨⟨margin, hmargin, ?_⟩, hJ hend⟩
  intro t
  obtain ⟨hlo, hhi⟩ := hpath t
  exact ⟨by linarith, by linarith⟩

/-- Enlarging the spatial corridor and endpoint window preserves an open
complete-segment entrance event. -/
theorem fullSegmentCorridorReturnEvent_mono_bounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    fullSegmentCorridorReturnEvent X start length
        lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      fullSegmentCorridorReturnEvent X start length
        lower₂ upper₂ coreLower₂ coreUpper₂ := by
  apply segmentCorridorEndpointEvent_mono X start length hlower hupper
  intro x hx
  exact ⟨lt_of_le_of_lt hcoreLower hx.1,
    lt_of_lt_of_le hx.2 hcoreUpper⟩

/-- Enlarging a corridor and a left-open, right-closed endpoint window
preserves the corresponding complete-segment event. -/
theorem fullSegmentCorridorIocReturnEvent_mono_bounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    fullSegmentCorridorIocReturnEvent X start length
        lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      fullSegmentCorridorIocReturnEvent X start length
        lower₂ upper₂ coreLower₂ coreUpper₂ := by
  apply segmentCorridorEndpointEvent_mono X start length hlower hupper
  intro x hx
  exact ⟨lt_of_le_of_lt hcoreLower hx.1,
    le_trans hx.2 hcoreUpper⟩

end ProbabilityTheory

end
