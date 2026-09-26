import Probability.BranchingRandomWalk.PointProcess.Representation.MonotoneEnumeration
import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import MeasureTheory.BranchingWalk.Ordered

/-!
# Monotone slot enumerations on the real line

This file specializes `MonotoneEnumeration` to the thesis's real child-slot
vocabulary. The structure itself is generic in the mark type and the ordering
relation; the results here use `ℝ`, the ordered slot set, and the measurability
of the real Dirac-sum point measure.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



/-- The point-process law associated with a random point measure.  This is
the semantic law used in the thesis; the slot law is an implementation law. -/
noncomputable def pointProcessLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Ξ : RealStepPointProcess Ω) : Measure (Measure ℝ) :=
  P.map Ξ

instance pointProcessLaw.isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Ξ : RealStepPointProcess Ω)
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (pointProcessLaw P Ξ) := by
  unfold pointProcessLaw
  infer_instance

/-- The left-to-right enumeration pushes forward to the ordered slot law. -/
theorem MonotoneEnumeration.markLaw_ordered
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (P : Measure Ω)
    [IsProbabilityMeasure P] :
    r.markLaw P orderedSteps = 1 := by
  rw [MonotoneEnumeration.markLaw,
    Measure.map_apply r.measurable_toStep orderedSteps_measurable]
  have hpre : r.toStep ⁻¹' orderedSteps = Set.univ := by
    ext ω
    exact ⟨fun _ => trivial, fun _ =>
      ⟨r.presence_parent ω, r.rel_ordered ω⟩⟩
  rw [hpre]
  simp

theorem MonotoneEnumeration.nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel) (ω : Ω) :
    r.toStep ω ∈ nonemptySupport ↔ Ξ ω ≠ 0 := by
  rw [← r.measure_eq ω]
  have hzero := stepPointMeasure_eq_zero_iff (r.toStep ω)
  tauto

theorem MonotoneEnumeration.markLaw_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : P {ω | Ξ ω ≠ 0} = 1) :
    r.markLaw P nonemptySupport = 1 := by
  rw [MonotoneEnumeration.markLaw,
    Measure.map_apply r.measurable_toStep nonemptySupport_measurable]
  have hpre : r.toStep ⁻¹' nonemptySupport = {ω | Ξ ω ≠ 0} := by
    ext ω
    exact r.nonempty_iff ω
  rw [hpre, hP]

/-- Passing to the slot law preserves the distribution of the random point
measure. This is the law-level connection used by the marked-tree model. -/
theorem MonotoneEnumeration.map_pointMeasure_markLaw
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) :
    (r.markLaw P).map stepPointMeasure = P.map Ξ := by
  rw [MonotoneEnumeration.markLaw, Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [] with ω
    exact r.measure_eq ω
  · exact stepPointMeasure_measurable
  · exact r.measurable_toStep

theorem MonotoneEnumeration.pointProcessLaw_eq_markLaw_map
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω) :
    pointProcessLaw P Ξ = (r.markLaw P).map stepPointMeasure := by
  exact (r.map_pointMeasure_markLaw P).symm

/-! Any nonnegative measurable observable of the point measure has the same
integral under the abstract point-process law and under its slot encoding. -/
theorem MonotoneEnumeration.lintegral_pointMeasure_eq
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop} (r : MonotoneEnumeration (X := ℝ) Ξ rel)
    (P : Measure Ω)
    (F : Measure ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(P.map Ξ) =
      ∫⁻ ξ, F (stepPointMeasure (r.toStep ξ)) ∂P := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (∫⁻ η, F η ∂(r.markLaw P).map stepPointMeasure) =
        ∫⁻ ξ, F (stepPointMeasure ξ) ∂(r.markLaw P) :=
      MeasureTheory.lintegral_map hF stepPointMeasure_measurable
    _ = ∫⁻ ξ, F (stepPointMeasure (r.toStep ξ)) ∂P := by
      unfold MonotoneEnumeration.markLaw
      exact MeasureTheory.lintegral_map
        (hF.comp stepPointMeasure_measurable)
        r.measurable_toStep

end ProbabilityTheory.BranchingRandomWalk
