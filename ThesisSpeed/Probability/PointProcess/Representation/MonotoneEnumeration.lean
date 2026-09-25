import ThesisSpeed.Probability.PointProcess.Slot.PointMeasure
import ThesisSpeed.Probability.PointProcess.Realization.BranchingStep
import ThesisSpeed.Probability.PointProcess.Slot.Order

/-!
# Measurable monotone slot enumerations of an abstract point process

This file states the exact bridge between a measure-valued point process and
the optional-slot model used by the marked tree.

The mark type `X` is an explicit parameter, so no particular real line is
built into the definition. The ordering relation on the marks is a second
parameter: `rel = (· ≤ ·)` gives the paper's left-to-right enumeration and the
flipped relation gives the right-to-left mirror. By
`branchingStepPrefixAntitone_iff_orderDual`, the mirror is the same condition
read in the dual order, so the definition singles out no direction. Existence
of a representation is a separate theorem obligation.
-/

open MeasureTheory

namespace ThesisSpeed

/-- A measurable monotone optional-slot enumeration whose Dirac sum is the
given measure-valued map, pointwise in the sample. The relation `rel` orders
the present slots, and the presence set is required to be a prefix. -/
structure MonotoneEnumeration {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (rel : X → X → Prop) where
  toStep : Ω → BranchingStep ℕ X
  measurable_toStep : Measurable toStep
  presence_prefix : ∀ ω, branchingStepPresencePrefix (toStep ω)
  rel_ordered : ∀ ω, branchingStepPrefixRel rel (toStep ω)
  measure_eq : ∀ ω, branchingStepPointMeasure (toStep ω) = ν ω

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

/-- The concrete child-mark law induced by a representation. -/
noncomputable def MonotoneEnumeration.markLaw
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} {rel : X → X → Prop}
    (r : MonotoneEnumeration ν rel) (P : Measure Ω) :
    Measure (BranchingStep ℕ X) :=
  P.map r.toStep

instance {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} {rel : X → X → Prop}
    (r : MonotoneEnumeration ν rel) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (r.markLaw P) := by
  unfold MonotoneEnumeration.markLaw
  infer_instance

/-- The left-to-right enumeration pushes forward to the ordered slot law. -/
theorem MonotoneEnumeration.markLaw_ordered
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (P : Measure Ω)
    [IsProbabilityMeasure P] :
    r.markLaw P orderedBranchingSteps = 1 := by
  rw [MonotoneEnumeration.markLaw,
    Measure.map_apply r.measurable_toStep orderedBranchingSteps_measurable]
  have hpre : r.toStep ⁻¹' orderedBranchingSteps = Set.univ := by
    ext ω
    exact ⟨fun _ => trivial, fun _ =>
      ⟨r.presence_prefix ω, r.rel_ordered ω⟩⟩
  rw [hpre]
  simp

theorem MonotoneEnumeration.nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel) (ω : Ω) :
    r.toStep ω ∈ childNonempty ↔ Ξ ω ≠ 0 := by
  rw [← r.measure_eq ω]
  have hzero := branchingStepPointMeasure_eq_zero_iff (r.toStep ω)
  tauto

theorem MonotoneEnumeration.markLaw_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : P {ω | Ξ ω ≠ 0} = 1) :
    r.markLaw P childNonempty = 1 := by
  rw [MonotoneEnumeration.markLaw,
    Measure.map_apply r.measurable_toStep childNonempty_measurable]
  have hpre : r.toStep ⁻¹' childNonempty = {ω | Ξ ω ≠ 0} := by
    ext ω
    exact r.nonempty_iff ω
  rw [hpre, hP]

/-- Passing to the slot law preserves the distribution of the random point
measure. This is the law-level connection used by the marked-tree model. -/
theorem MonotoneEnumeration.map_pointMeasure_markLaw
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) :
    (r.markLaw P).map branchingStepPointMeasure = P.map Ξ := by
  rw [MonotoneEnumeration.markLaw, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [] with ω
    exact r.measure_eq ω
  · exact branchingStepPointMeasure_measurable
  · exact r.measurable_toStep

theorem MonotoneEnumeration.pointProcessLaw_eq_markLaw_map
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) :
    pointProcessLaw P Ξ = (r.markLaw P).map branchingStepPointMeasure := by
  exact (r.map_pointMeasure_markLaw P).symm

/-! Any nonnegative measurable observable of the point measure has the same
integral under the abstract point-process law and under its slot encoding. -/
theorem MonotoneEnumeration.lintegral_pointMeasure_eq
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealBranchingStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω)
    (F : Measure ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(P.map Ξ) =
      ∫⁻ ξ, F (branchingStepPointMeasure (r.toStep ξ)) ∂P := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (∫⁻ η, F η ∂(r.markLaw P).map branchingStepPointMeasure) =
        ∫⁻ ξ, F (branchingStepPointMeasure ξ) ∂(r.markLaw P) :=
      MeasureTheory.lintegral_map hF branchingStepPointMeasure_measurable
    _ = ∫⁻ ξ, F (branchingStepPointMeasure (r.toStep ξ)) ∂P := by
      unfold MonotoneEnumeration.markLaw
      exact MeasureTheory.lintegral_map
        (hF.comp branchingStepPointMeasure_measurable)
        r.measurable_toStep

end ThesisSpeed
