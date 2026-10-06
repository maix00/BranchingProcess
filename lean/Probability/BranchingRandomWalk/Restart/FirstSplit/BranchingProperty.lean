/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.FirstSplit
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization

/-!
# Branching at the selected population's first split

At the observable completion of the first split, the two canonically selected
sibling roots have fresh independent descendant fields.  The statement is
restricted to samples on which the split occurs at a finite generation; no
children are postulated on samples where the selected population becomes
empty or never splits.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

theorem selectedPopulation_firstSplit_subtree_vector_factorization
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (A : Set (Mark α (Step α X)))
    (B : Set (Fin 2 → TreeNode α → Step α X))
    (hA : MeasurableSet[
      (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] A)
    (hB : MeasurableSet B) :
    stepFieldLaw μ
        ((A ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤}) ∩
          selectedSubtreeStepFieldVector
            (selectedPopulationFirstSplitRoots R) ⁻¹' B) =
      stepFieldLaw μ
        (A ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤}) *
          (Measure.infinitePi (fun _ : Fin 2 => stepFieldLaw μ)) B := by
  let σ := selectedPopulationSplitCompletion R
  let roots := selectedPopulationFirstSplitRoots R
  have hσ : IsStoppingTime (generationFiltration (M := Step α X)) σ :=
    selectedPopulationSplitCompletion_isStoppingTime R hR
  have hcount : (Set.range roots).Countable := by
    exact Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  have hfiber : ∀ r : Fin 2 → TreeNode α,
      MeasurableSet[hσ.measurableSpace] {ω | roots ω = r} := by
    intro r
    exact selectedPopulationFirstSplitRoots_fiber_measurable R hR r
  have hdepth : ∀ ω (n : ℕ), σ ω = (n : WithTop ℕ) →
      ∀ i : Fin 2, (roots ω i).length = n := by
    intro ω n htime
    exact selectedPopulationFirstSplitRoots_depth R ω n htime
  have hinj : ∀ ω, σ ω ≠ ⊤ → Function.Injective (roots ω) := by
    intro ω hfinite
    exact selectedPopulationFirstSplitRoots_injective_of_finite R ω hfinite
  exact stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ σ hσ roots hcount hfiber hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk
