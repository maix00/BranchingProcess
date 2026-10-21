/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
public import Probability.Ergodic.Kingman.Core
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayBounds
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.Subadditivity

/-!
# Auxiliary limit statements for the repaired array

- `repairedInfiniteSelection_tendsto_invariant_integrable`: the normalized
  repaired array converges almost surely under the invariant, integrable
  subadditive-cocycle hypotheses.
- `repairedInfiniteSelectionSubadditiveArray_eq_of_allGood`: on an
  environment whose batches are all valid, the repaired and original block
  arrays agree.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

lemma repairedInfiniteSelection_tendsto_invariant_integrable {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ G : GenerationEnvironment N → ℝ,
      (G ∘ generationEnvironmentShift =ᵐ[generationEnvironmentLaw μ N] G) ∧
      Integrable G (generationEnvironmentLaw μ N) ∧
      ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
        atTop (𝓝 (G ω)) := by
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  exact ProbabilityTheory.tendsto_kingman
    (generationEnvironmentLaw_shift_measurePreserving μ N)
    (repairedInfiniteSelection_isSubadditiveCocycle hN) hint hbdd

/-- In the i.i.d. generation environment the invariant Kingman limit is
almost surely constant, giving the scalar-speed form of the theorem. -/
lemma repairedInfiniteSelectionSubadditiveArray_eq_of_allGood {N : ℕ}
    (hN : 0 < N) (ω : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t))
    (start length : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN ω start length =
      infiniteSelectionSubadditiveArray hN ω hgood start length := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  have hseq : repairedGenerationBatchSeq ω = ω := by
    funext t
    exact repairGenerationBatch_eq_of_repairable (ω t) (hgood t)
  unfold infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  apply congrArg (fun state : Fin N → ℝ => -state ⟨0, hN⟩)
  exact infiniteOffspringRun_congr
    (fun t => repairedGenerationBatchSeq ω (start + t))
    (fun t => ω (start + t))
    (by
      funext t
      exact congrFun hseq (start + t))
    (fun t => repairedGenerationBatchSeq_good ω (start + t))
    (fun t => hgood (start + t))
    (fun _ => 0)
    length

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
