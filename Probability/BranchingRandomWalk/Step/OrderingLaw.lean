module

public import Probability.BranchingRandomWalk.Step.Ordering
public import Probability.BranchingRandomWalk.Step.PointMeasure

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

instance StepLaw.sorted.isProbabilityMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ]
    (L : StepLaw ι κ X) [IsProbabilityMeasure L.raw] :
    IsProbabilityMeasure L.sorted := by
  unfold StepLaw.sorted
  infer_instance

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

end ProbabilityTheory.BranchingRandomWalk
