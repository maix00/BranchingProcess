import Probability.BranchingRandomWalk.Step.Ordering
import Probability.BranchingRandomWalk.Step.PointMeasure

/-!
# Branching laws presented through a measurable ordering

The raw child law is never assumed to use ordered slots. A `StepLaw` contains
that raw measure together with deterministic measurable code that lists every
realized child in increasing order. All indexed variables `Ξᵢ` are read only
after applying this code. An ordering implementation may act as the identity
on inputs that are already ordered.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A raw branching-step law together with the measurable ordering used to
interpret its indexed children. -/
structure StepLaw (ι κ X : Type*) [MeasurableSpace X] [LT κ] [LE X] where
  raw : Measure (Combinatorics.Branching.Step ι X)
  ordering : MeasurableStepOrdering ι κ X

/-- The law of the measurably sorted child step. -/
noncomputable def StepLaw.sorted
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) :
    Measure (Combinatorics.Branching.Step κ X) :=
  L.raw.map L.ordering

instance StepLaw.sorted.isProbabilityMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) [IsProbabilityMeasure L.raw] :
    IsProbabilityMeasure L.sorted := by
  unfold StepLaw.sorted
  infer_instance

/-- The optional indexed variable `Ξᵢ`, always read after measurable sorting. -/
def StepLaw.displacement?
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) (i : κ) :
    Combinatorics.Branching.Step ι X → Option X :=
  fun ξ => L.ordering ξ i

theorem StepLaw.displacement?_measurable
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) (i : κ) :
    Measurable (L.displacement? i) :=
  (measurable_pi_apply i).comp L.ordering.measurable_ordered

/-- The total indexed variable `Ξᵢ` with absent slots assigned the additive
zero. This convention is used only after sorting. -/
def StepLaw.displacement
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X] [Zero X]
    (L : StepLaw ι κ X) (i : κ) :
    Combinatorics.Branching.Step ι X → X :=
  fun ξ => value' (L.ordering ξ) i

theorem StepLaw.displacement_measurable
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X] [Zero X]
    (L : StepLaw ι κ X) (i : κ) :
    Measurable (L.displacement i) :=
  (value'_measurable i).comp L.ordering.measurable_ordered

/-- Every sample of the sorted law is ordered. -/
theorem StepLaw.sorted_ordered
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) (hmeas : MeasurableSet
      (orderedSteps : Set (Combinatorics.Branching.Step κ X))) :
    L.sorted orderedSteps = L.raw Set.univ := by
  rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
    hmeas]
  have hpre : L.ordering ⁻¹' orderedSteps = Set.univ := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact L.ordering.isOrdered ξ
  rw [hpre]

/-- Sorting preserves the branching point measure sample by sample. -/
theorem StepLaw.sorted_pointMeasure
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X]
    (L : StepLaw ι κ X) (ξ : Combinatorics.Branching.Step ι X) :
    stepPointMeasure (L.ordering ξ) = stepPointMeasure ξ :=
  L.ordering.pointMeasure_ordered ξ

/-- Sorting neither creates nor removes the event that a step has a child. -/
theorem StepLaw.nonempty_ordering_iff
    {ι κ X : Type*} [MeasurableSpace X] [LT κ] [LE X] [Zero X]
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

/-- The nonempty-child probability is invariant under measurable sorting. -/
theorem StepLaw.sorted_nonemptySupport
    {ι κ X : Type*} [MeasurableSpace X] [Countable κ]
    [LT κ] [LE X] [Zero X] (L : StepLaw ι κ X) :
    L.sorted nonemptySupport = L.raw nonemptySupport := by
  rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
    nonemptySupport_measurable]
  congr 1
  ext ξ
  exact L.nonempty_ordering_iff ξ

/-- The boundary exponential sum is insensitive to sorting. -/
theorem StepLaw.totalChildWeight_ordering
    {ι κ : Type*} [LT κ] (L : StepLaw ι κ ℝ)
    (ξ : Combinatorics.Branching.Step ι ℝ) :
    totalChildWeight (L.ordering ξ) = totalChildWeight ξ := by
  rw [← lintegral_stepPointMeasure_exp (L.ordering ξ),
    ← lintegral_stepPointMeasure_exp ξ, L.sorted_pointMeasure ξ]

end ProbabilityTheory.BranchingRandomWalk
