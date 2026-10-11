/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Ordering
public import Probability.BranchingRandomWalk.Step.PointMeasure
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Combinatorics.BranchingWalk.Step.Map

/-!
# Branching laws presented through a measurable scalar ordering

A raw child law is never assumed to use ordered slots. A `StepLaw` stores an
abstract mark law, a measurable real potential, and deterministic measurable
code that lists every realized child increasingly by that potential. Indexed
variables are read only after applying this code.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
open Combinatorics.Branching

structure StepLaw (ι κ X : Type*) [MeasurableSpace X] [LT κ] where
  potential : Potential X
  raw : Measure (Combinatorics.Branching.Step ι X)
  ordering : MeasurableStepOrdering ι κ X potential

noncomputable def StepLaw.sorted {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) : Measure (Combinatorics.Branching.Step κ X) :=
  L.raw.map L.ordering

/-- The law of ordered children after projecting their marks through the
law's scalar potential. This keeps child slots and multiplicities unchanged
while putting the spatial increments in `ℝ`. -/
noncomputable def StepLaw.sortedPotentialImage {ι κ X : Type*}
    [MeasurableSpace X] [LT κ] (L : StepLaw ι κ X) :
    Measure (Combinatorics.Branching.Step κ ℝ) :=
  L.sorted.map (fun ξ => ξ.map L.potential)

instance StepLaw.sorted.isProbabilityMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) [IsProbabilityMeasure L.raw] :
    IsProbabilityMeasure L.sorted := by
  unfold StepLaw.sorted
  infer_instance

instance StepLaw.sortedPotentialImage.isProbabilityMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) [IsProbabilityMeasure L.raw] :
    IsProbabilityMeasure L.sortedPotentialImage := by
  unfold StepLaw.sortedPotentialImage
  exact (Measure.isProbabilityMeasure_map_iff
    (Step.map_measurable L.potential.measurable_toFun).aemeasurable).2 inferInstance

def StepLaw.displacement? {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (i : κ) :
    Combinatorics.Branching.Step ι X → Option X :=
  fun ξ => L.ordering ξ i

theorem StepLaw.displacement?_measurable
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (i : κ) : Measurable (L.displacement? i) :=
  (measurable_pi_apply i).comp L.ordering.measurable_ordered

/-- The real indexed displacement `φ(Ξᵢ)`, assigning zero to absence. -/
def StepLaw.displacement {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (i : κ) :
    Combinatorics.Branching.Step ι X → ℝ :=
  fun ξ => (L.ordering ξ).potentialValue' L.potential i

theorem StepLaw.displacement_measurable
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (i : κ) : Measurable (L.displacement i) :=
  (Step.potentialValue'_measurable L.potential i).comp
    L.ordering.measurable_ordered

theorem StepLaw.sorted_orderedBy
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X)
    (hmeas : MeasurableSet
      {ξ : Combinatorics.Branching.Step κ X | ξ.IsOrderedBy L.potential}) :
    L.sorted {ξ | ξ.IsOrderedBy L.potential} = L.raw Set.univ := by
  rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered hmeas]
  have hpre : L.ordering ⁻¹' {ξ | ξ.IsOrderedBy L.potential} = Set.univ := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact L.ordering.isOrderedBy ξ
  rw [hpre]

theorem StepLaw.sorted_pointMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (ξ : Combinatorics.Branching.Step ι X) :
    stepPointMeasure (L.ordering ξ) = stepPointMeasure ξ :=
  L.ordering.pointMeasure_ordered ξ

theorem StepLaw.nonempty_ordering_iff
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (ξ : Combinatorics.Branching.Step ι X) :
    L.ordering ξ ∈ nonemptySupport ↔ ξ ∈ nonemptySupport := by
  constructor
  · intro hord
    by_contra hraw
    have hzero : stepPointMeasure ξ = 0 :=
      (stepPointMeasure_eq_zero_iff ξ).2 hraw
    have hordzero : stepPointMeasure (L.ordering ξ) = 0 := by
      rw [L.sorted_pointMeasure ξ, hzero]
    exact (stepPointMeasure_eq_zero_iff (L.ordering ξ)).1 hordzero hord
  · rintro ⟨j, y, hj⟩
    obtain ⟨i, hi⟩ := L.ordering.covers ξ j y hj
    exact ⟨i, y, hi⟩

theorem StepLaw.sorted_nonemptySupport
    {ι κ X : Type*} [MeasurableSpace X] [Countable κ]
    [LT κ] (L : StepLaw ι κ X) :
    L.sorted nonemptySupport = L.raw nonemptySupport := by
  rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
    nonemptySupport_measurable]
  congr 1
  ext ξ
  exact L.nonempty_ordering_iff ξ

theorem StepLaw.sortedPotentialImage_nonemptySupport
    {ι κ X : Type*} [MeasurableSpace X] [Countable κ] [LT κ]
    (L : StepLaw ι κ X) :
    L.sortedPotentialImage nonemptySupport = L.sorted nonemptySupport := by
  rw [StepLaw.sortedPotentialImage,
    Measure.map_apply (Step.map_measurable L.potential.measurable_toFun)
      nonemptySupport_measurable]
  congr 1
  ext ξ
  simp [nonemptySupport]

theorem StepLaw.sortedPotentialImage_orderedBy
    {ι κ X : Type*} [MeasurableSpace X] [Countable κ] [LT κ]
    (L : StepLaw ι κ X) :
    L.sortedPotentialImage (orderedBySteps realPotential) = L.sorted Set.univ := by
  rw [StepLaw.sortedPotentialImage,
    Measure.map_apply (Step.map_measurable L.potential.measurable_toFun)
      (orderedBySteps_measurable realPotential)]
  have hpre :
      (fun ξ : Combinatorics.Branching.Step κ X => ξ.map L.potential) ⁻¹'
        orderedBySteps realPotential = orderedBySteps L.potential := by
    ext ξ
    simp [Step.IsOrderedBy, Step.map_map, realPotential]
  rw [hpre]
  calc
    L.sorted (orderedBySteps L.potential) = L.raw Set.univ :=
      L.sorted_orderedBy (orderedBySteps_measurable L.potential)
    _ = L.sorted Set.univ := by
      rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
        MeasurableSet.univ]
      simp

theorem Step.totalPotentialWeight_map
    {κ X : Type*} [MeasurableSpace X] (φ : Potential X)
    (ξ : Combinatorics.Branching.Step κ X) :
    totalPotentialWeight realPotential (-1) (ξ.map φ) =
      totalPotentialWeight φ (-1) ξ := by
  unfold totalPotentialWeight
  apply tsum_congr
  intro i
  cases h : ξ i <;>
    simp [realizedPotentialWeight, Step.map, Step.potentialValue',
      Step.potentialAt?, realPotential, survive, h]

theorem StepLaw.pointMeasureFunctional_ordering
    {ι κ X Y : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (F : Measure X → Y)
    (ξ : Combinatorics.Branching.Step ι X) :
    F (stepPointMeasure (L.ordering ξ)) = F (stepPointMeasure ξ) := by
  rw [L.sorted_pointMeasure ξ]

theorem StepLaw.totalChildWeight_ordering
    {ι κ : Type*} [LT κ] (L : StepLaw ι κ ℝ)
    (ξ : Combinatorics.Branching.Step ι ℝ) :
    totalChildWeight (L.ordering ξ) = totalChildWeight ξ := by
  rw [← lintegral_stepPointMeasure_exp (L.ordering ξ),
    ← lintegral_stepPointMeasure_exp ξ, L.sorted_pointMeasure ξ]

/-- The complete exponential potential weight is invariant under the
ordering rule because the rule preserves the child's point measure. -/
theorem StepLaw.totalPotentialWeight_ordering
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) (ξ : Combinatorics.Branching.Step ι X) :
    totalPotentialWeight L.potential (-1) (L.ordering ξ) =
      totalPotentialWeight L.potential (-1) ξ := by
  calc
    totalPotentialWeight L.potential (-1) (L.ordering ξ) =
        ∫⁻ x, ProbabilityTheory.PointProcess.exponentialWeight
          L.potential (-1) x ∂stepPointMeasure (L.ordering ξ) := by
      simpa [totalPotentialWeight] using
        (lintegral_stepPointMeasure_potential L.potential (-1)
          (L.ordering ξ) (f := fun _ => (1 : ENNReal)) measurable_const).symm
    _ = ∫⁻ x, ProbabilityTheory.PointProcess.exponentialWeight
          L.potential (-1) x ∂stepPointMeasure ξ := by
      rw [L.sorted_pointMeasure ξ]
    _ = totalPotentialWeight L.potential (-1) ξ := by
      simpa [totalPotentialWeight] using
        (lintegral_stepPointMeasure_potential L.potential (-1) ξ
          (f := fun _ => (1 : ENNReal)) measurable_const)

/-- Boundary normalization is preserved when passing from raw children to
their measurable ordered realization. -/
theorem StepLaw.sorted_hasBoundaryNormalization
    {ι κ X : Type*} [Countable ι] [Countable κ] [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X)
    (h : HasBoundaryNormalization L.potential L.raw) :
    HasBoundaryNormalization L.potential L.sorted := by
  change (∫⁻ η, totalPotentialWeight L.potential (-1) η
      ∂Measure.map L.ordering L.raw) = 1
  rw [lintegral_map (totalPotentialWeight_measurable L.potential (-1))
    L.ordering.measurable_ordered]
  calc
    (∫⁻ ξ, totalPotentialWeight L.potential (-1)
        (L.ordering ξ) ∂L.raw) =
      ∫⁻ ξ, totalPotentialWeight L.potential (-1) ξ ∂L.raw := by
        apply lintegral_congr
        intro ξ
        exact L.totalPotentialWeight_ordering ξ
    _ = 1 := h

/-- Projecting the ordered offspring law through its potential preserves the
boundary normalization as an ordinary real-displacement law. -/
theorem StepLaw.sortedPotentialImage_hasBoundaryNormalization
    {ι κ X : Type*} [MeasurableSpace X] [Countable ι] [Countable κ] [LT κ]
    (L : StepLaw ι κ X)
    (hboundary : HasBoundaryNormalization L.potential L.raw) :
    HasBoundaryNormalization realPotential L.sortedPotentialImage := by
  change (∫⁻ ξ, totalPotentialWeight realPotential (-1) ξ
      ∂L.sortedPotentialImage) = 1
  rw [StepLaw.sortedPotentialImage,
    lintegral_map (totalPotentialWeight_measurable realPotential (-1))
      (Step.map_measurable L.potential.measurable_toFun)]
  calc
    (∫⁻ ξ, totalPotentialWeight realPotential (-1)
        (ξ.map L.potential) ∂L.sorted) =
      ∫⁻ ξ, totalPotentialWeight L.potential (-1) ξ ∂L.sorted := by
        apply lintegral_congr
        intro ξ
        exact Step.totalPotentialWeight_map L.potential ξ
    _ = 1 := L.sorted_hasBoundaryNormalization hboundary

end ProbabilityTheory.BranchingRandomWalk
