/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayBounds
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
public import Probability.Ergodic.Kingman.Core
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Subadditive cocycle properties of the repaired array

- `repairedInfiniteSelectionSubadditiveArray_subadditive`: for `m,n ≥ 0`,
  `A ω s (m+n) ≤ A ω s m + A ω (s+m) n`.
- `repairedInfiniteSelectionSubadditiveArray_suffix`: shifting the
  environment agrees with advancing the starting generation.
- `generationEnvironmentShift_iterate`: the `n`-fold generation shift is
  `ω (n + t)` at time `t`.
- `repairedInfiniteSelection_isSubadditiveCocycle`: the repaired array is a
  subadditive cocycle over the generation shift.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

lemma repairedInfiniteSelectionSubadditiveArray_subadditive
    {N : ℕ} (hN : 0 < N) (ω : GenerationEnvironment N)
    (start firstLength secondLength : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN ω start
        (firstLength + secondLength) ≤
      repairedInfiniteSelectionSubadditiveArray hN ω start firstLength +
        repairedInfiniteSelectionSubadditiveArray hN ω (start + firstLength)
          secondLength := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  exact infiniteSelectionSubadditiveArray_subadditive hN
    (repairedGenerationBatchSeq ω) (repairedGenerationBatchSeq_good ω)
    start firstLength secondLength

/-- Starting a repaired environment at a later generation agrees with
advancing the block's start time. -/
lemma repairedInfiniteSelectionSubadditiveArray_suffix
    {N : ℕ} (hN : 0 < N) (ω : GenerationEnvironment N)
    (shift start length : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN
        (fun t => ω (shift + t)) start length =
      repairedInfiniteSelectionSubadditiveArray hN ω (shift + start) length := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  change infiniteSelectionSubadditiveArray hN
      (fun t => repairGenerationBatch (ω (shift + t)))
      (fun t => repairedGenerationBatchSeq_good (fun t => ω (shift + t)) t)
      start length =
    infiniteSelectionSubadditiveArray hN
      (fun t => repairGenerationBatch (ω t))
      (fun t => repairedGenerationBatchSeq_good ω t)
      (shift + start) length
  exact infiniteSelectionSubadditiveArray_shift_covariant hN
    (fun t => repairGenerationBatch (ω t))
    (fun t => repairedGenerationBatchSeq_good ω t)
    shift start length

/-- Iterating the one-sided environment shift by `m` is the same as dropping
the first `m` generations. -/
lemma generationEnvironmentShift_iterate {N : ℕ}
    (m : ℕ) (ω : GenerationEnvironment N) :
    (generationEnvironmentShift^[m]) ω = fun t => ω (m + t) := by
  induction m generalizing ω with
  | zero =>
      funext t
      simp
  | succ m ih =>
      funext t
      rw [Function.iterate_succ_apply]
      rw [ih (generationEnvironmentShift ω)]
      simp only [generationEnvironmentShift]
      congr 1
      omega

/-- The measurable repaired block array is a subadditive cocycle over the
generation shift, so it can be passed directly to the repository's Kingman
theorem. -/
lemma repairedInfiniteSelection_isSubadditiveCocycle {N : ℕ}
    (hN : 0 < N) :
    IsSubadditiveCocycle (generationEnvironmentShift :
      GenerationEnvironment N → GenerationEnvironment N)
      (fun n ω => repairedInfiniteSelectionSubadditiveArray hN ω 0 n) := by
  refine ⟨?_⟩
  intro m n ω
  calc
    repairedInfiniteSelectionSubadditiveArray hN ω 0 (m + n) ≤
        repairedInfiniteSelectionSubadditiveArray hN ω 0 m +
          repairedInfiniteSelectionSubadditiveArray hN ω m n := by
      simpa using repairedInfiniteSelectionSubadditiveArray_subadditive
        hN ω 0 m n
    _ = repairedInfiniteSelectionSubadditiveArray hN ω 0 m +
        repairedInfiniteSelectionSubadditiveArray hN
          ((generationEnvironmentShift^[m]) ω) 0 n := by
      congr 1
      rw [generationEnvironmentShift_iterate]
      simpa [Nat.zero_add, Nat.add_zero] using
        (repairedInfiniteSelectionSubadditiveArray_suffix hN ω m 0 n).symm

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
