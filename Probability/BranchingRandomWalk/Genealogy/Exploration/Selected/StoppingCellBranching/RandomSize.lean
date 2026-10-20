/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingCellBranching.Lemmas.Branches
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.StoppingPopulation

/-!
# Random-cardinality branching for the selected population

The public declaration in namespace `ProbabilityTheory.BranchingRandomWalk` is
`selectedPopulation_random_size_branching μ N x τ hτ hfinite`. For every
finite population value $s$, it gives an injective enumeration of the roots
and the cellwise product law; it also states that the population cells
partition every stopped-past event in measure:
\[
  \sum_s \nu_m\!\left(A\cap
      \{\operatorname{selectedPopulationAt}(N,x,\tau)=s\}\right)
  =\nu_m(A),
\]
where $\nu_m=\operatorname{finiteRootStepFieldLaw}(\mu,m)$. The cellwise
factorization is
\[
  \nu_m\!\left((A\cap\{\operatorname{selectedPopulationAt}=s\})
      \cap\Phi_u^{-1}(B)\right)
  =\nu_m\!\left(A\cap\{\operatorname{selectedPopulationAt}=s\}\right)
      \left(\nu^{\otimes |s|}\right)(B),
\]
where $\nu=\operatorname{stepFieldLaw}(\mu)$ and, for the enumerated roots
$u_i=(r_i,v_i)$, $\Phi_u(\omega)(i,v)=\omega(r_i,v_i\mathbin{++}v)$. The
assumptions require an everywhere-finite stopping time; the selected
population is measurable at that stopping time and every selected address
has depth $\tau$.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- The stopped selected population satisfies the abstract
cellwise branching theorem.  This is the concrete interface used by later
coupling arguments. -/
private lemma selectedPopulation_stopped_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
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
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤) :
    (∀ s : Finset (RootAddress m ℕ),
      ∃ roots : Fin s.card → RootAddress m ℕ,
        s = Finset.univ.image roots ∧
        ∀ (A : Set (FiniteRootStepField m ℕ ℝ))
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
    (∀ A : Set (FiniteRootStepField m ℕ ℝ),
      MeasurableSet[hτ.measurableSpace] A →
      (∑' s : Finset (RootAddress m ℕ),
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
