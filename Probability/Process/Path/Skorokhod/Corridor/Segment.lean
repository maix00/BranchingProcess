/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Skorokhod.RationalTime
public import Topology.Cadlag.Skorokhod.Corridor.Dense
public import Probability.Process.Corridor.Segment
public import Mathlib.Topology.UnitInterval

/-!
# Full-path corridor events on a time segment

The statement of a corridor event quantifies over the complete càdlàg
segment. A countable-coordinate description is used only to establish its
measurability and independence consequences.

## Public declarations

- `ProbabilityTheory.isCadlag_segmentIncrement`: a càdlàg process path
  restricts and recenters to a càdlàg path on any finite segment.
- `ProbabilityTheory.mem_fullSegmentCorridorEvent_iff_rational`:
  on càdlàg samples, membership in a positive-margin full-segment corridor is
  equivalent to its rational-coordinate conditions.
- `ProbabilityTheory.nullMeasurableSet_fullSegmentCorridorEvent`:
  the full-segment corridor event is null-measurable for a.s. càdlàg paths
  with a.e.-measurable coordinates.
- `ProbabilityTheory.mem_fullSegmentCorridorReturnEvent_iff_rational` and
  `ProbabilityTheory.mem_fullSegmentCorridorIocReturnEvent_iff_rational`:
  the open and left-open/right-closed terminal-window events have the matching
  rational-coordinate characterizations.
- `ProbabilityTheory.measure_fullSegmentCorridorIocReturnEvent_eq_rational`
  and `ProbabilityTheory.measure_fullSegmentCorridorReturnEvent_eq_rational`:
  the complete-path and rational-coordinate events have equal probabilities
  under a.s. càdlàg paths.
- `ProbabilityTheory.nullMeasurableSet_fullSegmentCorridorReturnEvent` and
  `ProbabilityTheory.nullMeasurableSet_fullSegmentCorridorIocReturnEvent`:
  both terminal-window events are null-measurable under the same coordinate
  measurability and path-regularity hypotheses.

The segment increment is
`\(\Delta X_{s,\ell}(t)=X_{s+\ell t}-X_s\)`. The full corridor event is
`\(\{\omega\mid\exists\eta>0,\ \forall t\in[0,1],\
a+\eta\le\Delta X_{s,\ell}(t,\omega)\le b-\eta\}\)`;
the return versions additionally impose
`\(\Delta X_{s,\ell}(1)\in(c,d)\)` or `\((c,d]\)`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem isCadlag_segmentIncrement {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    IsCadlag (segmentIncrement X start length ω) := by
  let clock : unitInterval → ℝ≥0 :=
    fun t => start + length * unitInterval.toNNReal t
  have hclockMono : Monotone clock := by
    intro s t hst
    have hst' : unitInterval.toNNReal s ≤ unitInterval.toNNReal t := by
      exact hst
    simpa [clock, add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hst' length.property) start
  have hclockCont : Continuous clock := by
    dsimp [clock]
    exact continuous_const.add
      (continuous_const.mul unitInterval.toNNReal_continuous)
  have hcomp := hω.comp_monotone_continuous hclockMono hclockCont
  have htranslated : IsCadlag (fun t : unitInterval =>
      X (clock t) ω - X start ω) :=
    hcomp.continuous_comp (g := fun x : ℝ => x - X start ω) (by fun_prop)
  change IsCadlag (fun t : unitInterval =>
    X (start + length * unitInterval.toNNReal t) ω - X start ω)
  simpa [clock] using htranslated

/-- At a càdlàg sample, the full-path event agrees exactly with its
countable-coordinate positive-margin description. -/
theorem mem_fullSegmentCorridorEvent_iff_rational
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    ω ∈ fullSegmentCorridorEvent X start length lower upper ↔
      (fun q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ∈
        Skorokhod.rationalCoordinateCorridorWithMargin lower upper := by
  let f : CadlagPath unitInterval ℝ :=
    ⟨segmentIncrement X start length ω,
      isCadlag_segmentIncrement X start length ω hω⟩
  have hbridge := Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff
    f lower upper
  simpa only [fullSegmentCorridorEvent, Set.mem_ofPred_eq,
    Skorokhod.rangeInOpenInterval, f,
    segmentIncrement, RationalCoordinate.toNNReal, unitInterval.toNNReal]
    using hbridge.symm

/-- Full-segment corridor events are measurable up to a null set when the
sample paths are càdlàg almost surely. -/
theorem nullMeasurableSet_fullSegmentCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper : ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    NullMeasurableSet
      (fullSegmentCorridorEvent X start length lower upper) P := by
  let rationalEvent : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  have hmap : AEMeasurable
      (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) P := by
    exact AEMeasurable.of_eval fun q => (hX _).sub (hX start)
  have hrational : NullMeasurableSet rationalEvent P :=
    hmap.nullMeasurableSet_preimage
      (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin lower upper)
  have heq : rationalEvent =ᵐ[P]
      fullSegmentCorridorEvent X start length lower upper := by
    filter_upwards [hcadlag] with ω hω
    exact propext ((mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).symm)
  exact hrational.congr heq

theorem mem_fullSegmentCorridorReturnEvent_iff_rational
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    ω ∈ fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper ↔
      (fun q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ∈
        Skorokhod.rationalCoordinateCorridorReturnWithMargin
          lower upper coreLower coreUpper := by
  rw [fullSegmentCorridorReturnEvent,
    Skorokhod.rationalCoordinateCorridorReturnWithMargin]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_Ioo]
  have htop : unitInterval.toNNReal ⊤ = 1 := unitInterval.toNNReal_one
  constructor
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mp hcorridor, by simpa [segmentIncrement,
        RationalCoordinate.toNNReal_top, htop] using hend⟩
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mpr hcorridor, by simpa [segmentIncrement,
        RationalCoordinate.toNNReal_top, htop] using hend⟩

/-- On a càdlàg sample, the complete corridor with a left-open,
right-closed terminal window is determined by its rational coordinates. -/
theorem mem_fullSegmentCorridorIocReturnEvent_iff_rational
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    ω ∈ fullSegmentCorridorIocReturnEvent X start length
        lower upper coreLower coreUpper ↔
      (fun q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
          lower upper coreLower coreUpper := by
  rw [fullSegmentCorridorIocReturnEvent,
    Skorokhod.rationalCoordinateCorridorIocReturnWithMargin]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  have htop : unitInterval.toNNReal ⊤ = 1 := unitInterval.toNNReal_one
  constructor
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mp hcorridor, by simpa [segmentIncrement,
        RationalCoordinate.toNNReal_top, htop] using hend⟩
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mpr hcorridor, by simpa [segmentIncrement,
        RationalCoordinate.toNNReal_top, htop] using hend⟩

/-- For almost surely càdlàg paths, the complete Ioc-return event and its
countable-coordinate description have the same probability. -/
theorem measure_fullSegmentCorridorIocReturnEvent_eq_rational
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    P ((fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω -
        X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lower upper coreLower coreUpper) =
      P (fullSegmentCorridorIocReturnEvent X start length
        lower upper coreLower coreUpper) := by
  apply measure_congr
  filter_upwards [hcadlag] with ω hω
  exact propext (mem_fullSegmentCorridorIocReturnEvent_iff_rational
    X start length lower upper coreLower coreUpper ω hω).symm

/-- For almost surely càdlàg paths, the complete open-endpoint corridor
event and its countable-coordinate description have the same probability. -/
theorem measure_fullSegmentCorridorReturnEvent_eq_rational
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    P ((fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω -
        X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper) =
      P (fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper) := by
  apply measure_congr
  filter_upwards [hcadlag] with ω hω
  exact propext (mem_fullSegmentCorridorReturnEvent_iff_rational
    X start length lower upper coreLower coreUpper ω hω).symm

theorem nullMeasurableSet_fullSegmentCorridorReturnEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    NullMeasurableSet (fullSegmentCorridorReturnEvent X start length
      lower upper coreLower coreUpper) P := by
  let rationalEvent : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  have hmap : AEMeasurable
      (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) P := by
    exact AEMeasurable.of_eval fun q => (hX _).sub (hX start)
  have hrational : NullMeasurableSet rationalEvent P :=
    hmap.nullMeasurableSet_preimage
      (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper)
  have heq : rationalEvent =ᵐ[P]
      fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper := by
    filter_upwards [hcadlag] with ω hω
    exact propext ((mem_fullSegmentCorridorReturnEvent_iff_rational
      X start length lower upper coreLower coreUpper ω hω).symm)
  exact hrational.congr heq

/-- The left-open, right-closed endpoint version is null-measurable for an
almost surely càdlàg process with measurable coordinates. -/
theorem nullMeasurableSet_fullSegmentCorridorIocReturnEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    NullMeasurableSet
      (fullSegmentCorridorIocReturnEvent X start length
        lower upper coreLower coreUpper) P := by
  let rationalEvent : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lower upper coreLower coreUpper
  have hmap : AEMeasurable
      (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) P := by
    exact AEMeasurable.of_eval fun q => (hX _).sub (hX start)
  have hrational : NullMeasurableSet rationalEvent P :=
    hmap.nullMeasurableSet_preimage
      (Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
        lower upper coreLower coreUpper)
  have heq : rationalEvent =ᵐ[P]
      fullSegmentCorridorIocReturnEvent X start length
        lower upper coreLower coreUpper := by
    filter_upwards [hcadlag] with ω hω
    exact propext ((mem_fullSegmentCorridorIocReturnEvent_iff_rational
      X start length lower upper coreLower coreUpper ω hω).symm)
  exact hrational.congr heq

end ProbabilityTheory

end
