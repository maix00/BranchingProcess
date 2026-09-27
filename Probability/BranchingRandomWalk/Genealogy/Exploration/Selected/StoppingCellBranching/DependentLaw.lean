import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.DependentLaw
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingCellBranching.SelectedPopulation

/-!
# The dependent stopped branching law for the selected process

This specializes the abstract random-cardinality law to the selected
population.  It gives one random descendant-family object, rather than a
separate existential statement for every possible population cell.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- The descendant-family random variable of the selected population at a
finite stopping time is measurable on the full pre-sampled space. -/
theorem selectedPopulation_stoppedSubtrees_measurable
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤) :
    Measurable (stoppedPopulationSubtrees
      (selectedPopulationAt N x τ)) :=
  stoppedPopulationSubtrees_measurable τ hτ
    (selectedPopulationAt N x τ)
    (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)

/-- At a finite stopping time, the selected population's dependent descendant
family has the countable mixture of the appropriate finite product laws. -/
theorem selectedPopulation_stoppedSubtrees_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set (StoppedSubtreeFamily ℝ)) (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ stoppedPopulationSubtrees
          (selectedPopulationAt N x τ) ⁻¹' B) =
      ∑' s : Finset (RootAddress m ℕ),
        finiteRootStepFieldLaw μ m
            (A ∩ {step | selectedPopulationAt N x τ step = s}) *
          (Measure.infinitePi
            (fun _ : Fin s.card => stepFieldLaw μ))
            ((stoppedSubtreeFamilyMk (X := ℝ) s.card) ⁻¹' B) := by
  exact stoppedPopulationSubtrees_factorization μ τ hτ hfinite
    (selectedPopulationAt N x τ)
    (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)
    (selectedPopulationAt_depth N x τ) A hA B hB

end ProbabilityTheory.BranchingRandomWalk
