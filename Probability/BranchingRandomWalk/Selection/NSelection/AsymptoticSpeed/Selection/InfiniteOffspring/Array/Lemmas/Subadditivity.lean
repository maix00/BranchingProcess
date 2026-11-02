/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Array.Basic

/-!
# Internal block-array proof lemmas

This module contains proof support for
`InfiniteOffspring.SubadditiveArray`. The block-minimum concatenation
inequality and deterministic-shift identity are the intermediate statements
used to prove the public subadditive-array properties. Keep reusable
branching-walk and random-walk results in their semantic modules instead.

## Internal proof declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.infiniteSelectionBlockMinimum_subadditive`
  states that, for a good offspring sequence, the leftmost endpoint satisfies
  $M(s,a+b)\ge M(s,a)+M(s+a,b)$, where $M(s,\ell)$ is
  `infiniteSelectionBlockMinimum` on the block starting at generation $s$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.infiniteSelectionBlockMinimum_shift_covariant`
  states that shifting the offspring sequence by $h$ and starting at $s$
  gives the same endpoint as the original sequence on the block starting at
  $h+s$.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

/-- Concatenating two blocks gives a superadditivity inequality for the
leftmost endpoint. -/
lemma infiniteSelectionBlockMinimum_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionBlockMinimum hN offspring hgood start
        (firstLength + secondLength) ≥
      infiniteSelectionBlockMinimum hN offspring hgood start firstLength +
        infiniteSelectionBlockMinimum hN offspring hgood (start + firstLength)
          secondLength := by
  let origin : Fin N := ⟨0, hN⟩
  have horigin : ∀ i : Fin N, origin ≤ i := by
    intro i
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.zero_le i.val
  let firstMarks := fun t => offspring (start + t)
  let firstGood := fun t => hgood (start + t)
  let state := infiniteOffspringRun firstMarks firstGood (fun _ => 0) firstLength
  have hstateMonotone : Monotone state := by
    exact infiniteOffspringRun_monotone firstMarks firstGood (fun _ => 0)
      (by intro i j hij; exact le_rfl) firstLength
  have hstateMin : ∀ i, state origin ≤ state i := by
    intro i
    exact hstateMonotone (horigin i)
  let commonStart : Fin N → ℝ := fun _ => state origin
  let laterMarks := fun t => offspring (start + firstLength + t)
  let laterGood := fun t => hgood (start + firstLength + t)
  let splitMarks := fun t => firstMarks (firstLength + t)
  let splitGood := fun t => firstGood (firstLength + t)
  have hcompare := infiniteOffspringRun_mono_initial laterMarks laterGood
    commonStart state hstateMin secondLength origin
  have hshift := infiniteOffspringRun_shift laterMarks laterGood (fun _ => 0)
    (state origin) secondLength
  have htranslated :
      infiniteOffspringRun laterMarks laterGood commonStart secondLength origin =
        infiniteOffspringRun laterMarks laterGood (fun _ => 0) secondLength origin +
          state origin := by
    have h := congrArg (fun f : Fin N → ℝ => f origin) hshift
    simpa [commonStart] using h
  have hsplit := infiniteOffspringRun_split firstMarks firstGood
    (fun _ => 0) firstLength secondLength
  have hsplit' :
      infiniteOffspringRun firstMarks firstGood (fun _ => 0)
        (firstLength + secondLength) =
      infiniteOffspringRun laterMarks laterGood state secondLength := by
    calc
      infiniteOffspringRun firstMarks firstGood (fun _ => 0)
          (firstLength + secondLength) =
        infiniteOffspringRun splitMarks splitGood state secondLength := by
          simpa [splitMarks, firstMarks, firstGood, state] using hsplit
      _ = infiniteOffspringRun laterMarks laterGood state secondLength :=
        infiniteOffspringRun_congr splitMarks laterMarks
          (by
            funext t
            dsimp [splitMarks, firstMarks, laterMarks]
            exact congrArg offspring (Nat.add_assoc start firstLength t).symm)
          splitGood laterGood state secondLength
  change infiniteOffspringRun firstMarks firstGood (fun _ => 0)
      (firstLength + secondLength) origin ≥
    infiniteOffspringRun firstMarks firstGood (fun _ => 0) firstLength origin +
      infiniteOffspringRun (fun t => offspring (start + firstLength + t))
        (fun t => hgood (start + firstLength + t)) (fun _ => 0)
        secondLength origin
  rw [hsplit']
  rw [add_comm (state origin)
    (infiniteOffspringRun laterMarks laterGood (fun _ => 0) secondLength origin)]
  rw [← htranslated]
  exact hcompare

/-- A deterministic shift of the generation environment shifts the starting
time of every block. This is the pathwise stationarity identity; a
measure-preserving law for the environment turns it into distributional
stationarity. -/
lemma infiniteSelectionBlockMinimum_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start length : ℕ) :
    infiniteSelectionBlockMinimum hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start length =
      infiniteSelectionBlockMinimum hN offspring hgood (shift + start) length := by
  unfold infiniteSelectionBlockMinimum
  have hrun := infiniteOffspringRun_congr
    (fun t => offspring (shift + (start + t)))
    (fun t => offspring (shift + start + t))
    (by
      funext t
      exact congrArg offspring (Nat.add_assoc shift start t).symm)
    (fun t => hgood (shift + (start + t)))
    (fun t => hgood (shift + start + t))
    (fun _ => 0)
    length
  exact congrArg (fun f : Fin N → ℝ => f ⟨0, hN⟩) hrun

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
