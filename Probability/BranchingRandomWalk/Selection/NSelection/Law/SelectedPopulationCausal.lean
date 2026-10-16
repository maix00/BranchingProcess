/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Law.CausalPopulation

/-!
# Causal interface for first-N populations

The totalized first-N population is a finite causal population on the same
pre-sampled field.  This interface lets it serve as the source process in
rank-installed couplings.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
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
      rw [RootIndexed.childrenAtGeneration_eq_offspringAddressSet n
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
  let candidates := RootIndexed.childrenAtGeneration n
    (RootIndexed.selectedPopulationTotalized N roots initial d φ n field) field
  by_cases hgood : IsLowerFiniteBy value candidates
  · have hspec := RootIndexed.selectedPopulationTotalized_succ_spec
      N roots initial d φ n field (by simpa [value, candidates] using hgood)
    exact hspec.card_le
  · simp [RootIndexed.selectedPopulationTotalized,
      selectFirstNFromSetTotalized_empty_of_not_lowerFinite,
      value, candidates, hgood]

/-- At generation zero, inclusion of root sets gives the identity spatial
domination between their initial populations. -/
noncomputable def RootIndexed.initialPopulationInjectionOfSubset
    {Root α Mark Position Value : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (initial : Root → Position)
    (sourceRoots targetRoots : Finset Root)
    (hroots : sourceRoots ⊆ targetRoots)
    (sourceField targetField : RootIndexed.StepField Root α Mark) :
    Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial sourceField)
        (RootIndexed.initialPopulation (α := α) sourceRoots))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial targetField)
        (RootIndexed.initialPopulation (α := α) targetRoots)) () where
  toFun := id
  mapsTo := by
    intro p hp
    change p ∈ RootIndexed.initialPopulation (α := α) targetRoots
    change p ∈ RootIndexed.initialPopulation (α := α) sourceRoots at hp
    rw [RootIndexed.mem_initialPopulation_iff] at hp ⊢
    obtain ⟨r, hr, rfl⟩ := hp
    exact ⟨r, hroots hr, rfl⟩
  injOn := Set.injOn_id _
  dominates := by
    intro p hp
    change φ (RootIndexed.position initial d targetField p.1 p.2) ≤
      φ (RootIndexed.position initial d sourceField p.1 p.2)
    obtain ⟨r, _, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hp
    simp [RootIndexed.position]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
