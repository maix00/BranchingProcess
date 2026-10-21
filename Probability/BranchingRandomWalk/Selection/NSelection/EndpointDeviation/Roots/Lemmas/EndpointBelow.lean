/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Law.SelectedPopulationCoupling

/-!
# Endpoint event transfer under nested-root coupling

The public declaration in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` is
`RootIndexed.selectedPopulationNestedRoots_endpointBelow_ae`. Under a
probability measure with boundary normalization and
`sourceRoots ⊆ targetRoots\), it states that almost surely under the common
two-copy root-indexed law, the implication

\[
\begin{aligned}
&\exists p\in\operatorname{Selected}_N(\text{sourceRoots},n):
  \operatorname{position}(p)\le x\\
&\qquad\Longrightarrow
  \exists q\in\operatorname{RestartedSelected}_N(\text{targetRoots},n):
  \operatorname{position}(q)\le x
\end{aligned}
\]

holds. The target population and position are those of the rank-installed
restarted process driven by the same source population and common field. This
is the endpoint-event step used by the outer root-monotonicity theorem.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- Almost surely under the common two-copy field, every selected endpoint
below a threshold from the smaller root set has a selected endpoint below the
same threshold in the rank-installed process from the containing root set. -/
lemma RootIndexed.selectedPopulationNestedRoots_endpointBelow_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (sourceRoots targetRoots : Finset Root)
    (hroots : sourceRoots ⊆ targetRoots)
    (initialPosition : Root → ℝ) (n : ℕ) (x : ℝ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      (∃ p : RootIndexed.TreeNode Root α,
        p ∈ RootIndexed.selectedPopulationTotalized N sourceRoots
          initialPosition id id n (RootIndexed.StepField.left field) ∧
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 ≤ x) →
      (∃ q : RootIndexed.TreeNode Root α,
        q ∈ RootIndexed.restartedRealPositionMatchedPopulation N targetRoots
          initialPosition id
          (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
            initialPosition id id k (RootIndexed.StepField.left field)) n field ∧
        RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionMatchedField N targetRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤ x) := by
  have hcoupled := RootIndexed.selectedPopulationNestedRootsCoupledInjection_ae
    μ hnorm N sourceRoots targetRoots hroots initialPosition n
  filter_upwards [hcoupled] with field hcoupled
  intro hbelow
  rcases hbelow with ⟨p, hp, hpx⟩
  rcases hcoupled with ⟨hmap⟩
  let q := hmap p
  have hq : q ∈ RootIndexed.restartedRealPositionMatchedPopulation N targetRoots
      initialPosition id
      (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
        initialPosition id id k (RootIndexed.StepField.left field)) n field := by
    exact hmap.mapsTo (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
      using hp)
  have hposition :
      RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionMatchedField N targetRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 := by
    have hp' : p ∈
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field))
          (RootIndexed.selectedPopulationTotalized N sourceRoots
            initialPosition id id n (RootIndexed.StepField.left field))).particles () := by
      simpa [Combinatorics.Branching.Selection.Coupling.populationCloud] using hp
    have hdom := hmap.dominates p hp'
    simpa [Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField,
      ProbabilityTheory.BranchingRandomWalk.RootIndexed.position,
      ProbabilityTheory.BranchingRandomWalk.RootIndexed.displace] using hdom
  exact ⟨q, hq, hposition.trans hpx⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
