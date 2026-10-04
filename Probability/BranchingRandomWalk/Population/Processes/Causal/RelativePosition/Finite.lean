/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Basic
import Combinatorics.BranchingWalk.Step.ExponentialWeight

/-!
# Finiteness adapters for causal relative-position populations

This file converts directional finiteness of offspring levels into finite
relative-position slices.  It does not specialize the construction to real
weights.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.RandomWalk

attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable def ofRestartedPositionSetsOfUpperFinite
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position] [LinearOrder Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → Position)
    (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (hlevel : ∀ (n : ℕ) (field : RootIndexed.StepField Root α Mark)
        (p : RootIndexed.TreeNode Root α), p.2.length = n → ∀ (a : Position),
      {i | survive (field p.1 p.2) i ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (restartAnchor cutoff (n + 1)) (n + 1)
          (p.1, p.2 ++ [i]) field ≤ a}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofRestartedPositionSets initialPosition d hd initial hinitialDepth
    cutoff window hwindow
  intro n parents field
  apply RootIndexed.childrenAtGeneration_filter_finite_of_upperBound
    n parents field
    (fun q => RootIndexed.relativePositionAtGeneration initialPosition d
      (restartAnchor cutoff (n + 1)) (n + 1) q field)
    (window (n + 1)) (upper (n + 1)) (hupper (n + 1))
  intro p _ hp a
  exact hlevel n field p hp a

/-- The directional finiteness premise can be checked on each mapped
branching step itself.  Translation from a parent position to its child does
not alter finiteness of lower levels. -/
noncomputable def ofRestartedPositionSetsOfStepLowerFinite
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position] [LinearOrder Position]
    [IsOrderedAddMonoid Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (upper : ℕ → Position)
    (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (hstep : ∀ (field : RootIndexed.StepField Root α Mark)
        (p : RootIndexed.TreeNode Root α) (a : Position),
      {i | survive ((field p.1 p.2).map d) i ∧
        value' ((field p.1 p.2).map d) i ≤ a}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofRestartedPositionSetsOfUpperFinite initialPosition d hd initial
    hinitialDepth cutoff window hwindow upper hupper
  intro n field p hp a
  let parentRelative := RootIndexed.relativePositionAtGeneration
    initialPosition d (restartAnchor cutoff (n + 1)) n p field
  apply (hstep field p (a - parentRelative)).subset
  intro i hi
  refine ⟨?_, ?_⟩
  · simpa using hi.1
  · apply le_sub_iff_add_le.mpr
    rw [add_comm]
    rw [← RootIndexed.relativePositionAtGeneration_child initialPosition d field
      (restartAnchor_succ_le_parent cutoff n) p hp i]
    exact hi.2

end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk
