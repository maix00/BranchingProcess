/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Population

/-!
# Causal interface for first-N populations

The totalized first-N population is a finite causal population on the same
pre-sampled field.  This interface lets it serve as the source process in
rank-installed couplings.


## Public declarations

The totalized first-\(N\) process is a finite causal source, and every
positive-generation slice obeys the capacity bound:

\[
\forall n,\omega,\quad
P_{n+1}(\omega)\text{ is finite},\qquad
|P_{n+1}(\omega)|\le N.
\]

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.selectedPopulationTotalizedSource`:
  views the totalized first-`N` population on the left coordinate of a
  two-copy pre-sampled field as a causal population.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.selectedPopulationTotalizedSource_finiteSlices`:
  proves that every generation slice of that causal source is finite.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.selectedPopulationTotalized_card_le`:
  every positive-generation totalized selected slice satisfies
  `card (selectedPopulationTotalized (n + 1) field) ≤ N`, including fields
  where the selector uses its empty-set fallback.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The totalized first-N population from a finite set of roots, viewed on
the left half of a two-copy pre-sampled field as a causal population. -/
noncomputable def RootIndexed.selectedPopulationTotalizedSource
    {Root α Mark Position Value : Type*}
    [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [MeasurableSpace Position] [AddCommMonoid Position]
    [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [SecondCountableTopology Value]
    [OrderClosedTopology Value] [MeasurableEq Value]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left := by
  let leftMeasurable (n : ℕ) : @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α Mark)
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n)
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n)
      RootIndexed.StepField.left := by
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α Mark →
          RootIndexed.StepField Root α Mark) by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable
      (X := Mark) Sum.inl n
  refine {
    toPopulation := ?_
    adapted := ?_
  }
  · intro field
    refine {
      particles := fun n =>
        ((RootIndexed.selectedPopulationTotalized N roots initial d φ n
          (RootIndexed.StepField.left field) :
            Finset (RootIndexed.TreeNode Root α)) :
          Set (RootIndexed.TreeNode Root α))
      depth := ?_
      successor := ?_
    }
    · intro n p hp
      exact RootIndexed.selectedPopulationTotalized_depth N roots initial d φ n
        (RootIndexed.StepField.left field) p hp
    · intro n p hp
      have hchild := RootIndexed.selectedPopulationTotalized_succ_subset N roots
        initial d φ n (RootIndexed.StepField.left field) hp
      rw [Combinatorics.Branching.Population.childrenAtGeneration_eq_offspringAddressSet n
        (RootIndexed.selectedPopulationTotalized N roots initial d φ n
          (RootIndexed.StepField.left field))
        (RootIndexed.StepField.left field)] at hchild
      · exact hchild
      · intro q hq
        exact RootIndexed.selectedPopulationTotalized_depth N roots initial d φ n
          (RootIndexed.StepField.left field) q hq
  · intro p n
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
      RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n
    have hmeas : Measurable[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n]
        (fun field => RootIndexed.selectedPopulationTotalized N roots initial
          d φ n (RootIndexed.StepField.left field)) := by
      exact (RootIndexed.selectedPopulationTotalized_adapted N roots initial d hd
        φ hφ n).comp (leftMeasurable n)
    exact (measurable_finset_iff.mp hmeas p)

/-- The selected causal source has finite slices on every raw field. -/
theorem RootIndexed.selectedPopulationTotalizedSource_finiteSlices
    {Root α Mark Position Value : Type*}
    [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [MeasurableSpace Position] [AddCommMonoid Position]
    [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [SecondCountableTopology Value]
    [OrderClosedTopology Value] [MeasurableEq Value]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    RootIndexed.CausalPopulation.FiniteSlices
      (RootIndexed.selectedPopulationTotalizedSource (Root := Root) (α := α)
        (Mark := Mark) (Position := Position) (Value := Value)
        N roots initial d hd φ hφ) := by
  intro n field
  change ((RootIndexed.selectedPopulationTotalized N roots initial d φ n
    (RootIndexed.StepField.left field) : Finset (RootIndexed.TreeNode Root α)) :
      Set (RootIndexed.TreeNode Root α)).Finite
  exact (RootIndexed.selectedPopulationTotalized N roots initial d φ n
    (RootIndexed.StepField.left field)).finite_toSet

/-- Every positive-generation slice of totalized first-N selection contains
at most N particles, including on raw fields where selection falls back to
the empty set. -/
theorem RootIndexed.selectedPopulationTotalized_card_le
    {Root α Mark Position Value : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n : ℕ) (field : RootIndexed.StepField Root α Mark) :
    (RootIndexed.selectedPopulationTotalized N roots initial d φ (n + 1)
      field).card ≤ N := by
  classical
  let value := RootIndexed.observedPositionAtGeneration initial d φ (n + 1) field
  let candidates := Combinatorics.Branching.Population.childrenAtGeneration n
    (RootIndexed.selectedPopulationTotalized N roots initial d φ n field) field
  by_cases hgood : IsLowerFiniteBy value candidates
  · have hspec := RootIndexed.selectedPopulationTotalized_succ_spec
      N roots initial d φ n field (by simpa [value, candidates] using hgood)
    exact hspec.card_le
  · simp [RootIndexed.selectedPopulationTotalized,
      selectFirstNFromSetTotalized_empty_of_not_lowerFinite,
      value, candidates, hgood]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
