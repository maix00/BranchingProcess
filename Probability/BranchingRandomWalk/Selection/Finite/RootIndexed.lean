/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.Finite.ByValue
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

/-!
# Root-indexed random finite selection by position

This module adapts measurable position processes on pre-sampled forests to
causal random finite selections. Deterministic selected-population maps stay
in the `NSelection` subtree.
-/

open MeasureTheory Combinatorics.UlamHarris

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Finite.RootIndexed

open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

noncomputable section

variable {Root α Mark Position Value : Type*}

/-- Dynamic leftmost selection is causal for the generation domain flow of an
arbitrary root-indexed pre-sampled forest. Countability is needed only by the
finite-set measurable encoding used by this concrete capacity selector. -/
noncomputable def leftmostBy
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalFiniteCapacitySelection ℕ
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.TreeNode Root α) N
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark)) :=
  CausalFiniteCapacitySelection.leftmostByOfMeasurableValue N
    (observedPositionAtGeneration initial d φ)
    (fun n p => hφ.comp
      (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
        initial d hd n p.1 p.2))

@[simp] theorem leftmostBy_select
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (s : Finset (RootIndexed.TreeNode Root α)) :
    (leftmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) s :=
  rfl

/-- The opposite spatial selection uses the same position process and changes
only its ordered observation to `OrderDual Value`. -/
noncomputable def rightmostBy
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalFiniteCapacitySelection ℕ
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.TreeNode Root α) N
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark)) :=
  leftmostBy N initial d hd
    (fun x => OrderDual.toDual (φ x)) hφ

@[simp] theorem rightmostBy_select
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (s : Finset (RootIndexed.TreeNode Root α)) :
    (rightmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (fun p => OrderDual.toDual
          (observedPositionAtGeneration initial d φ n ω p)) s :=
  rfl

end

end ProbabilityTheory.BranchingRandomWalk.Selection.Finite.RootIndexed
