module

public import Probability.BranchingRandomWalk.Spine.TiltedLaw
public import Probability.BranchingRandomWalk.Step.PointMeasure
public import Probability.PointProcess.Tilted

/-!
# Point-measure representation of the spine increment law

The abstract tilted law integrates against a random measure and has no atom
enumeration parameter.  A countable-slot branching step maps to that law, and
the resulting measure agrees with the slotwise construction.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

theorem lintegral_pointMeasure_tiltedLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X] [Zero X]
    (φ : Potential X) (θ : ℝ)
    (μ : Measure (Combinatorics.Branching.Step ι X))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ y, f y ∂PointProcess.tiltedLaw φ θ
        (μ.map stepPointMeasure)) =
      ∫⁻ ξ, ∑' i : ι, realizedPotentialWeight φ θ ξ i *
        f (ξ.potentialValue' φ i) ∂μ := by
  rw [PointProcess.lintegral_tiltedLaw φ.measurable_toFun θ _ hf]
  have hintegrand : Measurable (fun x : X =>
      PointProcess.exponentialWeight φ θ x * f (φ x)) :=
    (PointProcess.exponentialWeight_measurable φ.measurable_toFun θ).mul
      (hf.comp φ.measurable_toFun)
  have hmeasureFunctional : Measurable (fun ν : Measure X =>
      ∫⁻ x, PointProcess.exponentialWeight φ θ x * f (φ x) ∂ν) :=
    Measure.measurable_lintegral hintegrand
  rw [lintegral_map hmeasureFunctional stepPointMeasure_measurable]
  apply lintegral_congr
  intro ξ
  exact lintegral_stepPointMeasure_potential φ θ ξ hf

theorem pointMeasure_tiltedLaw_eq_tiltedPotentialLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X] [Zero X]
    (φ : Potential X) (θ : ℝ)
    (μ : Measure (Combinatorics.Branching.Step ι X)) :
    PointProcess.tiltedLaw φ θ (μ.map stepPointMeasure) =
      tiltedPotentialLaw φ θ μ := by
  ext s hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs]
  calc
    (∫⁻ a, s.indicator 1 a
        ∂PointProcess.tiltedLaw φ θ (μ.map stepPointMeasure)) =
        ∫⁻ ξ, ∑' i : ι, realizedPotentialWeight φ θ ξ i *
          s.indicator 1 (ξ.potentialValue' φ i) ∂μ :=
      lintegral_pointMeasure_tiltedLaw φ θ μ
        (measurable_const.indicator hs)
    _ = ∫⁻ a, s.indicator 1 a ∂tiltedPotentialLaw φ θ μ :=
      (lintegral_tiltedPotentialLaw φ θ μ _
        (measurable_const.indicator hs)).symm

theorem pointMeasure_hasNormalization
    {ι X : Type*} [Countable ι] [MeasurableSpace X] [Zero X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    PointProcess.HasNormalization φ (-1) (μ.map stepPointMeasure) := by
  unfold PointProcess.HasNormalization
  have hintegrand : Measurable (fun x : X =>
      PointProcess.exponentialWeight φ (-1) x) :=
    PointProcess.exponentialWeight_measurable φ.measurable_toFun (-1)
  have hmeasureFunctional : Measurable (fun ν : Measure X =>
      ∫⁻ x, PointProcess.exponentialWeight φ (-1) x ∂ν) :=
    Measure.measurable_lintegral hintegrand
  rw [lintegral_map hmeasureFunctional stepPointMeasure_measurable]
  simp_rw [show ∀ ξ : Combinatorics.Branching.Step ι X,
      (∫⁻ x, PointProcess.exponentialWeight φ (-1) x
          ∂stepPointMeasure ξ) = totalPotentialWeight φ (-1) ξ by
    intro ξ
    simpa only [mul_one, totalPotentialWeight] using
      (lintegral_stepPointMeasure_potential φ (-1) ξ
        (f := fun _ => 1) measurable_const)]
  exact hboundary

theorem pointMeasure_tiltedLaw_isProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X] [Zero X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    IsProbabilityMeasure
      (PointProcess.tiltedLaw φ (-1) (μ.map stepPointMeasure)) :=
  PointProcess.tiltedLaw_isProbability φ.measurable_toFun (-1)
    (μ.map stepPointMeasure) (pointMeasure_hasNormalization φ μ hboundary)

end ProbabilityTheory.BranchingRandomWalk.Spine
