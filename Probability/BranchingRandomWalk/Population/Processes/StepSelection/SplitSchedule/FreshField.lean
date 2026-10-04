/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Roots
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Fresh fields obtained from successful split trials

The roots selected from the first successful fixed-age trial determine a
new finite root-indexed step field.  Its complete product law and its
independence from the generation domain flow follow from the abstract
selected-subtree theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The descendant fields below the roots supplied by the first successful
split trial. -/
noncomputable def freshField
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField (Fin N) α X :=
  RootIndexed.selectedSubtreeStepFieldVector
    (roots N R root duration target fallback) ω

/-- A successful-trial fresh field has the full `Fin N`-rooted product law.
The fallback hypotheses totalize the selector on the no-success event; they
are automatic once a suitable deterministic same-generation family is
provided. -/
theorem freshField_law
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (freshField N R root duration target fallback) =
      RootIndexed.stepFieldLaw (Root := Fin N) μ := by
  exact RootIndexed.selectedSubtreeStepFieldVector_law μ
    (roots N R root duration target fallback)
    (roots_range_countable N R root duration target fallback)
    (roots_fiber_adapted N R hR root duration target fallback)
    (roots_depth N R root duration target fallback hfallbackDepth)
    (roots_injective N R root duration target fallback hfallbackInjective)

/-- The successful-trial fresh field is independent of the generation
domain flow that selected its roots. -/
theorem freshField_independent
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration)
      (MeasurableSpace.comap
        (freshField N R root duration target fallback) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  exact RootIndexed.selectedSubtreeStepFieldVector_independent μ
    (roots N R root duration target fallback)
    (roots_range_countable N R root duration target fallback)
    (roots_fiber_adapted N R hR root duration target fallback)
    (roots_depth N R root duration target fallback hfallbackDepth)
    (roots_injective N R root duration target fallback hfallbackInjective)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
