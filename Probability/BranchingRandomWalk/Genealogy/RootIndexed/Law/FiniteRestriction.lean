/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

/-!
# Finite restrictions of root-indexed product laws

The public declarations in `ProbabilityTheory.BranchingRandomWalk` state:

- `RootIndexed.StepField.measurable_first`: restricting a field indexed by
  countably many roots to its first `m` roots is measurable, for any
  measurable mark space.
- `RootIndexed.StepField.measurePreserving_first μ m`: the same restriction
  sends the countable-root product law to the `Fin m` product law, namely
  `map (RootIndexed.StepField.first m)
  (RootIndexed.stepFieldLaw (Root := ℕ) μ) = finiteRootStepFieldLaw μ m`,
  when `μ` is a probability measure.

These restriction results apply to every measurable mark space; the endpoint
observable on the restricted field is handled in its endpoint module.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- Restricting a countable-root step field to its first `m` roots is
measurable. -/
theorem RootIndexed.StepField.measurable_first
    {α X : Type*} [MeasurableSpace X] (m : ℕ) :
    Measurable
      (RootIndexed.StepField.first m : CountableRootStepField α X →
        FiniteRootStepField m α X) := by
  rw [measurable_pi_iff]
  intro r
  rw [measurable_pi_iff]
  intro u
  exact (measurable_pi_apply u).comp (measurable_pi_apply (Fin.val r))

/-- Restriction to the first `m` roots preserves the product law. -/
theorem RootIndexed.StepField.measurePreserving_first
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (RootIndexed.StepField.first m)
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
      (finiteRootStepFieldLaw μ m) := by
  refine ⟨RootIndexed.StepField.measurable_first m, ?_⟩
  exact countableRootStepFieldLaw_first μ m

end ProbabilityTheory.BranchingRandomWalk
