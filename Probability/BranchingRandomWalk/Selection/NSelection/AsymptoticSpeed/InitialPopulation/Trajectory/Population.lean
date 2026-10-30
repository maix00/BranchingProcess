/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

public import Mathlib.Order.Defs.LinearOrder

/-!
# The selected population from a finite set of roots

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialPopulation`:
  the first $N$ particles selected from the $m$ roots at generation $n$,
  namely `selectedPopulationTotalized N Finset.univ (fun _ => 0) id id n field`.
  Thus
  \[
    P_n=\operatorname{selectedPopulationTotalized}
      (N,\mathrm{univ},0,\mathrm{id},\mathrm{id},n,\mathrm{field}).
  \]

-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.UlamHarris

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def smallInitialPopulation (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin m)) (fun _ => 0) id id n field

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
