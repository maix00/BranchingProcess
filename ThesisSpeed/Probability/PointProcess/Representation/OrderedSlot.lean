import ThesisSpeed.Probability.PointProcess.Slot.PointMeasure
import ThesisSpeed.Probability.PointProcess.Realization.BranchingStep
import ThesisSpeed.Probability.PointProcess.Slot.Order

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
    (Ξ : RealBranchingStepPointProcess Ω) where
  toMark : Ω → NatRealBranchingStep
  measurable_toMark : Measurable toMark
  ordered : ∀ ω, toMark ω ∈ orderedOffspring
  measure_eq : ∀ ω, offspringPointMeasure (toMark ω) = Ξ ω

/-- The point-process law associated with a random point measure.  This is
the semantic law used in the thesis; the slot law is an implementation law. -/
noncomputable def pointProcessLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Ξ : RealBranchingStepPointProcess Ω) : Measure (Measure ℝ) :=
  P.map Ξ

instance pointProcessLaw.isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Ξ : RealBranchingStepPointProcess Ω)
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (pointProcessLaw P Ξ) := by
  unfold pointProcessLaw
  infer_instance

/-- The concrete offspring-mark law induced by a representation. -/
noncomputable def OrderedSlotRepresentation.markLaw
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω) :
    Measure NatRealBranchingStep :=
  P.map r.toMark

instance {Ω : Type*} [MeasurableSpace Ω]
    {Ξ : RealBranchingStepPointProcess Ω} (r : OrderedSlotRepresentation Ξ)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (r.markLaw P) := by
  unfold OrderedSlotRepresentation.markLaw
  infer_instance

theorem OrderedSlotRepresentation.markLaw_ordered
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
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
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (ω : Ω) :
    r.toMark ω ∈ offspringNonempty ↔ Ξ ω ≠ 0 := by
  rw [← r.measure_eq ω]
  have hzero := offspringPointMeasure_eq_zero_iff (r.toMark ω)
  tauto

theorem OrderedSlotRepresentation.markLaw_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
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
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω) :
    (r.markLaw P).map offspringPointMeasure = P.map Ξ := by
  rw [OrderedSlotRepresentation.markLaw, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [] with ω
    exact r.measure_eq ω
  · exact offspringPointMeasure_measurable
  · exact r.measurable_toMark

theorem OrderedSlotRepresentation.pointProcessLaw_eq_markLaw_map
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω) :
    pointProcessLaw P Ξ = (r.markLaw P).map offspringPointMeasure := by
  exact (r.map_pointMeasure_markLaw P).symm

/-! Any nonnegative measurable observable of the point measure has the same
integral under the abstract point-process law and under its slot encoding. -/
theorem OrderedSlotRepresentation.lintegral_pointMeasure_eq
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : OrderedSlotRepresentation Ξ) (P : Measure Ω)
    (F : Measure ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(P.map Ξ) =
      ∫⁻ ξ, F (offspringPointMeasure (r.toMark ξ)) ∂P := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (∫⁻ η, F η ∂(r.markLaw P).map offspringPointMeasure) =
        ∫⁻ ξ, F (offspringPointMeasure ξ) ∂(r.markLaw P) :=
      MeasureTheory.lintegral_map hF offspringPointMeasure_measurable
    _ = ∫⁻ ξ, F (offspringPointMeasure (r.toMark ξ)) ∂P := by
      unfold OrderedSlotRepresentation.markLaw
      exact MeasureTheory.lintegral_map
        (hF.comp offspringPointMeasure_measurable)
        r.measurable_toMark

end ThesisSpeed
