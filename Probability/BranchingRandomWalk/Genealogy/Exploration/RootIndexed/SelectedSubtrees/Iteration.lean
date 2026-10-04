/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Iterated adaptive fresh subtree fields

Finite iteration of generation-measurable fresh-subtree replacement preserves
the complete root-indexed product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-! ## Iterated adaptive fresh fields -/

/-- Successively replace a field by a same-indexed family of fresh descendant
fields.  Stage `j` reads only the current field supplied to that stage. -/
def RootIndexed.iteratedSelectedSubtreeStepField
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α) :
    ℕ → RootIndexed.StepField Root α X →
      RootIndexed.StepField Root α X
  | 0 => id
  | j + 1 => RootIndexed.selectedSubtreeStepFieldVector (chosen j) ∘
      RootIndexed.iteratedSelectedSubtreeStepField chosen j

@[simp] theorem RootIndexed.iteratedSelectedSubtreeStepField_zero
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α) :
    RootIndexed.iteratedSelectedSubtreeStepField chosen 0 = id :=
  rfl

@[simp] theorem RootIndexed.iteratedSelectedSubtreeStepField_succ
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α) (j : ℕ) :
    RootIndexed.iteratedSelectedSubtreeStepField chosen (j + 1) =
      RootIndexed.selectedSubtreeStepFieldVector (chosen j) ∘
        RootIndexed.iteratedSelectedSubtreeStepField chosen j :=
  rfl

theorem RootIndexed.iteratedSelectedSubtreeStepField_measurable
    {Root α X : Type*} [MeasurableSpace X]
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α)
    (generation : ℕ → ℕ)
    (hcount : ∀ j, (Set.range (chosen j)).Countable)
    (hfiber : ∀ j roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (generation j)]
        {ω | chosen j ω = roots}) :
    ∀ j, Measurable
      (RootIndexed.iteratedSelectedSubtreeStepField chosen j) := by
  intro j
  induction j with
  | zero => exact measurable_id
  | succ j ih =>
      exact (RootIndexed.selectedSubtreeStepFieldVector_measurable
        (chosen j) (hcount j) (hfiber j)).comp ih

/-- Every finite iteration of adapted injective fresh-family replacement has
the original complete product law. -/
theorem RootIndexed.iteratedSelectedSubtreeStepField_law
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α)
    (generation : ℕ → ℕ)
    (hcount : ∀ j, (Set.range (chosen j)).Countable)
    (hfiber : ∀ j roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (generation j)]
        {ω | chosen j ω = roots})
    (hdepth : ∀ j ω i, (chosen j ω i).2.length = generation j)
    (hinj : ∀ j ω, Function.Injective (chosen j ω)) :
    ∀ j,
      (RootIndexed.stepFieldLaw (Root := Root) μ).map
          (RootIndexed.iteratedSelectedSubtreeStepField chosen j) =
        RootIndexed.stepFieldLaw (Root := Root) μ := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [RootIndexed.iteratedSelectedSubtreeStepField_succ,
        ← Measure.map_map
          (RootIndexed.selectedSubtreeStepFieldVector_measurable
            (chosen j) (hcount j) (hfiber j))
          (RootIndexed.iteratedSelectedSubtreeStepField_measurable
            chosen generation hcount hfiber j),
        ih,
        RootIndexed.selectedSubtreeStepFieldVector_law μ
          (chosen j) (hcount j) (hfiber j) (hdepth j) (hinj j)]

end ProbabilityTheory.BranchingRandomWalk
