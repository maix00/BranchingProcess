/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Predicate
import Probability.BranchingRandomWalk.Population.Processes.Causal.Genealogy
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.RelativePosition

/-!
# Basic causal relative-position constructions

This file defines the general set-valued killed populations obtained from
ancestral relative-position windows.  Finiteness and real-valued weights are
separate layers.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Walk

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Kill every child whose displacement from its `anchor n` ancestor lies
outside `window n`.  No order or real-valued structure is imposed on the
position space. -/
noncomputable def ofRelativePositionSets
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (anchor : ℕ → ℕ) (hanchor : ∀ n, anchor n ≤ n)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α Mark),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (anchor (n + 1)) (n + 1) q field ∈ window (n + 1)}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofPredicate (Root := Root) (α := α) (X := Mark)
    initial hinitialDepth
    (fun n field q =>
      RootIndexed.relativePositionAtGeneration initialPosition d
        (anchor n) n q field ∈ window n) hfinite
  intro n q
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n
  apply measurableSet_setOfPred.mp
  exact (RootIndexed.relativePositionAtGeneration_measurable
    initialPosition d hd (hanchor n) q) (hwindow n)

/-- Two-stage killed population: positions are viewed from the initial root
through `cutoff`, and from the generation-`cutoff` ancestor afterwards.  The
window function may impose narrower cuts exactly at `cutoff` and at a terminal
generation. -/
noncomputable def ofRestartedPositionSets
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommGroup Position] [MeasurableAdd₂ Position]
    [MeasurableSub₂ Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α Mark),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        RootIndexed.relativePositionAtGeneration initialPosition d
          (restartAnchor cutoff (n + 1)) (n + 1) q field ∈
            window (n + 1)}.Finite) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id :=
  ofRelativePositionSets initialPosition d hd initial hinitialDepth
    (restartAnchor cutoff) (restartAnchor_le cutoff)
    window hwindow hfinite

end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk
