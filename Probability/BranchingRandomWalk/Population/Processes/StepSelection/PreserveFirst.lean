/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Filter
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.FirstN

/-!
# Measurable first-child-preserving step rules

This construction retains the intrinsic first child whenever one exists and
applies a potential barrier to the rest of an intrinsic finite initial
segment.  Empty branching steps remain empty.  No raw child slot is
privileged.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.StepSelection

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The first-child-preserving potential rule is measurable. -/
theorem preserveFirstBelowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    Measurable
      (Step.FiniteSelection.preserveFirstBelowPotential
        N φ a hlevel).select := by
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => Step.FiniteSelection.admitsFirstNByPotential_of_level_finite
      k φ ξ (hlevel ξ)
  let first := Step.FiniteSelection.firstNByPotential 1 φ (admits 1)
  let initial := Step.FiniteSelection.firstNByPotential N φ (admits N)
  have hfirst : Measurable first.select :=
    firstNByPotential_measurable 1 φ (admits 1)
  have hinitial : Measurable initial.select :=
    firstNByPotential_measurable N φ (admits N)
  have hbelow : Measurable (initial.belowPotential φ a).select :=
    belowPotential_measurable initial hinitial φ a
  have hunion : Measurable
      (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    measurable_of_countable _
  have h := hunion.comp (hfirst.prodMk hbelow)
  change Measurable (fun ξ =>
    first ξ ∪ (initial.belowPotential φ a) ξ) at h
  simpa only [Step.FiniteSelection.preserveFirstBelowPotential,
    first, initial, admits] using h

end ProbabilityTheory.BranchingRandomWalk.StepSelection
