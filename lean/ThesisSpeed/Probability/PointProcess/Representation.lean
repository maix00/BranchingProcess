import ThesisSpeed.Probability.PointProcess.Measure
import ThesisSpeed.Probability.PointProcess.Enumeration.Order

/-!
# Measurable slot representations of an abstract point process

This file states the exact bridge required between the thesis input, a
measure-valued point process, and the optional-slot model used by the marked
tree. Existence of this representation is a separate theorem obligation.
-/

open MeasureTheory

namespace ThesisSpeed

/-- A measurable ordered optional-slot enumeration whose Dirac sum is the
given abstract offspring point measure, pointwise in the sample. -/
structure OrderedSlotRepresentation {Ω : Type*} [MeasurableSpace Ω]
    (Ξ : OffspringPointProcess Ω) where
  toMark : Ω → OffspringMark
  measurable_toMark : Measurable toMark
  ordered : ∀ ω, toMark ω ∈ orderedOffspring
  measure_eq : ∀ ω, offspringPointMeasure (toMark ω) = Ξ ω

/-- The concrete offspring-mark law induced by a representation. -/
noncomputable def OrderedSlotRepresentation.markLaw
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : OffspringPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω) :
    Measure OffspringMark :=
  P.map r.toMark

instance {Ω : Type*} [MeasurableSpace Ω]
    {Ξ : OffspringPointProcess Ω} (r : OrderedSlotRepresentation Ξ)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (r.markLaw P) := by
  unfold OrderedSlotRepresentation.markLaw
  infer_instance

theorem OrderedSlotRepresentation.markLaw_ordered
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : OffspringPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω)
    [IsProbabilityMeasure P] :
    r.markLaw P orderedOffspring = 1 := by
  rw [OrderedSlotRepresentation.markLaw,
    Measure.map_apply r.measurable_toMark orderedOffspring_measurable]
  have hpre : r.toMark ⁻¹' orderedOffspring = Set.univ := by
    ext ω
    simp [r.ordered]
  rw [hpre]
  simp

theorem OrderedSlotRepresentation.nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : OffspringPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (ω : Ω) :
    r.toMark ω ∈ offspringNonempty ↔ Ξ ω ≠ 0 := by
  rw [← r.measure_eq ω]
  have hzero := offspringPointMeasure_eq_zero_iff (r.toMark ω)
  tauto

theorem OrderedSlotRepresentation.markLaw_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : OffspringPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hP : P {ω | Ξ ω ≠ 0} = 1) :
    r.markLaw P offspringNonempty = 1 := by
  rw [OrderedSlotRepresentation.markLaw,
    Measure.map_apply r.measurable_toMark offspringNonempty_measurable]
  have hpre : r.toMark ⁻¹' offspringNonempty = {ω | Ξ ω ≠ 0} := by
    ext ω
    exact r.nonempty_iff ω
  rw [hpre, hP]

/-- Passing to the slot law preserves the distribution of the random point
measure. This is the law-level connection used by the marked-tree model. -/
theorem OrderedSlotRepresentation.map_pointMeasure_markLaw
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : OffspringPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω) :
    (r.markLaw P).map offspringPointMeasure = P.map Ξ := by
  rw [OrderedSlotRepresentation.markLaw, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [] with ω
    exact r.measure_eq ω
  · exact offspringPointMeasure_measurable
  · exact r.measurable_toMark

end ThesisSpeed
