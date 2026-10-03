import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.Enumeration
import Probability.Process.HittingTime.Declarations

/-!
# Population cells at a stopping generation

The cells `{population = s}` refine any stopped-measurable event, are pairwise
disjoint, and sum to that event. This is the random-cardinality measure argument,
independent of any concrete particle-selection algorithm.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem abstractMultiRootStoppedCell_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (E : Set (FiniteRootStepField m ℕ X))
    (hE : MeasurableSet[hτ.measurableSpace] E) (n : ℕ) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      (E ∩ {step | τ step = (n : WithTop ℕ)}) :=
  (hτ.measurableSet_inter_eq_iff E n).1
    (hE.inter (hτ.measurable
      (measurableSet_singleton (n : WithTop ℕ))))

theorem abstractStoppedPopulation_cells_partition
    {m : ℕ} {X : Type*}
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (A : Set (FiniteRootStepField m ℕ X)) :
    Pairwise (fun s t =>
      Disjoint (A ∩ {step | population step = s})
        (A ∩ {step | population step = t})) ∧
      (⋃ s : Finset (Fin m × 𝕍),
        A ∩ {step | population step = s}) = A := by
  constructor
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro step hs ht
    exact hst (hs.2.symm.trans ht.2)
  · ext step
    constructor
    · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨s, hAstep, _⟩
      exact hAstep
    · intro hstep
      exact Set.mem_iUnion.mpr ⟨population step, hstep, rfl⟩

theorem abstractStoppedPopulation_cells_measure_sum
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (A : Set (FiniteRootStepField m ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∑' s : Finset (Fin m × 𝕍),
      finiteRootStepFieldLaw μ m (A ∩ {step | population step = s})) =
      finiteRootStepFieldLaw μ m A := by
  obtain ⟨hpair, hunion⟩ :=
    abstractStoppedPopulation_cells_partition population A
  have hmeas : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet (A ∩ {step | population step = s}) := by
    intro s
    exact (hτ.measurableSpace_le _ hA).inter
      (hτ.measurableSpace_le _ (hpopulation s))
  calc
    (∑' s : Finset (Fin m × 𝕍),
        finiteRootStepFieldLaw μ m (A ∩ {step | population step = s})) =
      finiteRootStepFieldLaw μ m (⋃ s : Finset (Fin m × 𝕍),
        A ∩ {step | population step = s}) :=
      (measure_iUnion hpair hmeas).symm
    _ = finiteRootStepFieldLaw μ m A := by rw [hunion]

end ProbabilityTheory.BranchingRandomWalk
