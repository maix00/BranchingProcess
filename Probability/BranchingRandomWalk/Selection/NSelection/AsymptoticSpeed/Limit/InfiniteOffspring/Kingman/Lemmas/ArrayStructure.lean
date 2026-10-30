/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.SubadditiveArray
import Probability.Ergodic.Kingman.Theorem
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Run
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import all Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayBounds

/-!
# Array identities and subadditive cocycle structure

For $0<N$, write $A_\omega(s,n)$ for the repaired selection array and
$(\theta\omega)(t)=\omega(t+1)$ for the generation shift.

## Internal proof declarations

- `repairedInfiniteSelectionSubadditiveArray_subadditive`:
  $A_\omega(s,m+n)\le A_\omega(s,m)+A_\omega(s+m,n)$.
- `repairedInfiniteSelectionSubadditiveArray_suffix`:
  shifting the environment by $k$ agrees with changing the starting generation
  from $s$ to $k+s$.
- `repairedInfiniteSelection_isSubadditiveCocycle`:
  the array defines a subadditive cocycle over $\theta$.
- `repairedInfiniteSelectionSubadditiveArray_eq_of_allGood`:
  on environments whose generations are all good, the repaired array agrees
  with the original selection array.

## Source

These internal array identities formalize the subadditivity and stationarity checks in
WANG Yiyang, *Asymptotic Speed of the \(N\)-Branching Random Walk with Infinite
Offspring*, Master's thesis, Fudan University (2026), Section 3.4.2,
Lemma 3.12.
-/

section

open MeasureTheory Filter
open scoped ENNReal Topology

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
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
private lemma generationEnvironmentShift_iterate {N : ℕ}
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
lemma. -/
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

/-- On an environment whose generations are all good, the repaired array
coincides with the original selection array. -/
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
