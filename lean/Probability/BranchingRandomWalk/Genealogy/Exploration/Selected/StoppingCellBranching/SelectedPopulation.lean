import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingCellBranching.Branches

/-!
# The selected population at a stopping time

The concrete selected population instantiates the abstract cellwise branching
theorem, and the random-cardinality interface packages the cellwise product law
together with the countable partition of probability.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


/-- The stopped selected population of the thesis satisfies the abstract
cellwise branching theorem.  This is the concrete interface used by later
coupling arguments. -/
theorem selectedPopulation_stopped_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
            ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m
            (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  apply multiRoot_stoppedPopulation_each_cell_branches μ τ hτ hfinite
    (selectedPopulationAt N x τ)
    (fun t => selectedPopulationAt_cell_measurable N x τ hτ hfinite t)
    (selectedPopulationAt_depth N x τ)

/-- Unified random-cardinality interface for the selected population: every
finite cell has a duplicate-free multi-root enumeration with the product
descendant law, and all cells form the countable probability partition. -/
theorem selectedPopulation_random_size_branching
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤) :
    (∀ s : Finset (RootAddress m),
      ∃ roots : Fin s.card → RootAddress m,
        s = Finset.univ.image roots ∧
        ∀ (A : Set (FiniteRootStepField m ℝ))
          (_ : MeasurableSet[hτ.measurableSpace] A)
          (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
          (_ : MeasurableSet B),
          finiteRootStepFieldLaw μ m
              ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
                multiRootSubtreeStepFieldVector roots ⁻¹' B) =
            finiteRootStepFieldLaw μ m
              (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
              (Measure.infinitePi
                (fun _ : Fin s.card => stepFieldLaw μ)) B) ∧
    (∀ A : Set (FiniteRootStepField m ℝ),
      MeasurableSet[hτ.measurableSpace] A →
      (∑' s : Finset (RootAddress m),
        finiteRootStepFieldLaw μ m
          (A ∩ {ω | selectedPopulationAt N x τ ω = s})) =
        finiteRootStepFieldLaw μ m A) := by
  constructor
  · intro s
    exact selectedPopulation_stopped_cell_branches μ N x τ hτ hfinite s
  · intro A hA
    exact multiRoot_stoppedPopulation_cells_measure_sum μ τ hτ
      (selectedPopulationAt N x τ)
      (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)
      A hA

end ProbabilityTheory.BranchingRandomWalk
