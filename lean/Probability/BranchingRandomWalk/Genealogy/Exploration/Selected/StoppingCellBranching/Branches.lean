import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingCellBranching.Factorization

/-!
# Every stopped population cell branches

Every cell of a stopped finite population admits a duplicate-free enumeration
whose descendant vector branches with the cell-dependent finite product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- Every cell of a stopped finite population admits an enumeration whose
descendant vector branches with the appropriate (cell-dependent) finite
product law. -/
theorem multiRoot_stoppedPopulation_each_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ}
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : FiniteRootStepField m ℕ ℝ → Finset (RootAddress m ℕ))
    (hpopulation : ∀ s : Finset (RootAddress m ℕ),
      MeasurableSet[hτ.measurableSpace] {ω | population ω = s})
    (hdepth : ∀ ω (u : RootAddress m ℕ), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
            ((A ∩ {ω | population ω = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m (A ∩ {ω | population ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    multiRoot_stoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s roots hcover hinj B hB⟩

end ProbabilityTheory.BranchingRandomWalk
