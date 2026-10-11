/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Speed.InitialPopulationTrajectory
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.SelectedPopulationBatch
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.KingmanInterface
import Probability.Sequence.IID.Law

/-!
# Speed after a smaller initial population reaches capacity

After the first capacity hit, the selected descendants form an exact-`N`
population.  This file transports the exact-`N` speed to that trajectory and
then back to the original finite-root population.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The offspring batches read from the spatially ranked population form an
i.i.d. generation environment with the exact-`N` law. -/
theorem selectedPopulationRankBatch_hasLaw_generationEnvironment
    (N : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × TreeNode ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × TreeNode ℕ)]
    [Countable (Fin N × TreeNode ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    HasLaw
      (fun field n => selectedRootBatch
        (selectedPopulationRankRoots N initial) n field)
      (generationEnvironmentLaw μ N)
      (RootIndexed.stepFieldLaw (Root := Fin N) μ) := by
  let chosen := selectedPopulationRankRoots N initial
  let P := RootIndexed.stepFieldLaw (Root := Fin N) μ
  have hcount : ∀ n, (Set.range (chosen n)).Countable := by
    intro n
    exact selectedPopulationRankRoots_countable N n initial
  have hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ) n]
      {field | chosen n field = roots} := by
    intro n roots
    exact selectedPopulationRankRoots_fiber_measurable N n initial roots
  have hdepth : ∀ n field i, (chosen n field i).2.length = n := by
    intro n field i
    exact selectedPopulationRankRoot_depth N n initial field i
  have hinj : ∀ n field, Function.Injective (chosen n field) := by
    intro n field
    exact selectedPopulationRankRoots_injective N n initial field
  have hindep : iIndepFun (selectedRootBatch chosen ·) P := by
    exact selectedPopulationRankBatch_iIndepFun N initial μ
  have hmeasAt := RootIndexed.measurable_selectedRootBatch_at_succ
    chosen hcount hfiber hdepth
  have hmeas (n : ℕ) : Measurable (selectedRootBatch chosen n) := by
    let F := RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ)
    exact (hmeasAt n).mono (F.le (n + 1)) le_rfl
  have hlaw (n : ℕ) : HasLaw (selectedRootBatch chosen n)
      (generationBatchLaw μ N) P := by
    refine ⟨(hmeas n).aemeasurable, ?_⟩
    change P.map (selectedRootBatch chosen n) = generationBatchLaw μ N
    simpa [P, chosen, generationBatchLaw] using
      (RootIndexed.selectedRootBatch_independent_and_law μ chosen
        hcount hfiber hdepth hinj n).2
  have hsequence := ProbabilityTheory.iIndepFun.hasLaw_iidSequenceLaw
    hindep hmeas hlaw
  simpa [generationEnvironmentLaw, generationBatchLaw,
    ProbabilityTheory.iidSequenceLaw] using hsequence

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
