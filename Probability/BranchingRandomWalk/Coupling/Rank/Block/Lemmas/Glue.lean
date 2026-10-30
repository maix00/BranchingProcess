/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Coupling.Rank.Block.Basic

/-!
# Internal rank-block gluing identity

This identity expands the coordinate gluing used at one recursive installation
step. It has one client in `Field/Ranked/Lemmas/RecursiveStep.lean`, so the
statement remains under this local `Lemmas/` directory.

For the block choice `B_n`, prior field `g`, and fallback field `f`, it states

\[
  \operatorname{glue}_n(g_{<n},B_n(f))
  = \operatorname{updateGeneration}_n
      (\operatorname{rankInstalledStepField}_n(f,g),g),
\]

provided `g` agrees with the fallback field on coordinates of depth at least
`n`.

## Internal declaration

- `RootIndexed.glue_rankBlockChoice_eq_updateGeneration` is the displayed
  one-step gluing identity.
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The block-coordinate construction is exactly the step-only
`updateGeneration` installation when the prior field still equals the
fallback copy at generation `n` and later. -/
lemma RootIndexed.glue_rankBlockChoice_eq_updateGeneration
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (base : RootIndexed.StepField (Root ⊕ Root) α X)
    (prior : RootIndexed.StepField Root α X)
    (hprior : ∀ r u, n ≤ u.length → prior r u = base (Sum.inr r) u) :
    RootIndexed.StepField.glue n (prior.past n)
        (RootIndexed.selectedCoordinateField
          (RootIndexed.rankBlockChoice n sourceValue targetValue source target)
          base) =
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
        (RootIndexed.rankInstalledStepField
          (fun _ => sourceValue base) (fun _ => targetValue base)
          (fun _ => source base) (fun _ => target base)
          (fun sample r u => sample (Sum.inl r) u)
          (fun _ => prior) base)
        prior := by
  funext r u
  by_cases hlt : u.length < n
  · simp [RootIndexed.StepField.glue, hlt,
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
      Nat.ne_of_lt hlt, RootIndexed.StepField.past]
  · have hle : n ≤ u.length := Nat.le_of_not_gt hlt
    by_cases heq : u.length = n
    · have htake : u.take n = u := by simp [heq]
      have hdrop : u.drop n = [] := by simp [heq]
      simp only [RootIndexed.StepField.glue,
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
        heq, ↓reduceIte, RootIndexed.selectedCoordinateField,
        RootIndexed.StepField.reindexCoordinates_apply, htake, hdrop,
        RootIndexed.rankBlockChoice]
      unfold RootIndexed.rankChoice
        RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate
      unfold RootIndexed.rankInstalledStepField valueAtMatchedRank
        Coupling.valueAtPreimage
      cases hpre : preimageByRank (sourceValue base) (targetValue base)
          (source base) (target base) (r, u) with
      | some p => simp [hpre]
      | none => simp [hpre, hprior r u hle]
    · have hgt : n < u.length := lt_of_le_of_ne hle (Ne.symm heq)
      have hdrop : u.drop n ≠ [] := by
        intro hnil
        have := congrArg List.length (List.take_append_drop n u)
        simp [hnil, List.length_take, Nat.min_eq_left hle] at this
        omega
      simp only [RootIndexed.StepField.glue, hlt, dite_false,
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
        heq, ↓reduceIte, RootIndexed.selectedCoordinateField,
        RootIndexed.StepField.reindexCoordinates_apply]
      cases hv : u.drop n with
      | nil => exact (hdrop hv).elim
      | cons i v =>
          simp only [RootIndexed.rankBlockChoice]
          have huv : u.take n ++ i :: v = u := by
            rw [← hv]
            exact List.take_append_drop n u
          rw [huv]
          exact (hprior r u hle).symm


end ProbabilityTheory.BranchingRandomWalk.Coupling
