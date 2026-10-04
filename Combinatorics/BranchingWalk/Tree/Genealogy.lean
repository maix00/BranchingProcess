/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Branching.Tree.Basic
public import Combinatorics.Branching.Basic
public import Combinatorics.BranchingWalk.Basic.SiblingClosed
public import Combinatorics.Branching.Map

/-!
# Branching trees and branching walks

A branching tree embeds into a branching walk with unit marks. Conversely,
the genealogy of a sibling-closed branching walk is a branching tree. This is
the deterministic seam between pure and spatial branching.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {α Mark Position : Type*} [LT α]

noncomputable def Tree.stepField (T : Tree α) : StepField α PUnit.{1} := by
  classical
  exact fun u i => if u ++ [i] ∈ T.carrier then some PUnit.unit.{1} else none

theorem Tree.survive_stepField_iff (T : Tree α)
    (u : TreeNode α) (i : α) :
    survive (T.stepField u) i ↔ u ++ [i] ∈ T.carrier := by
  classical
  simp [Tree.stepField, survive]

theorem Tree.surviveAlong_stepField_iff (T : Tree α) (u : TreeNode α) :
    surviveAlong T.stepField [] u ↔ u ∈ T.carrier := by
  induction u using List.reverseRecOn with
  | nil => simp [surviveAlong, T.root_mem]
  | append_singleton u i ih =>
      rw [surviveAlong_root_append_singleton_iff, ih,
        T.survive_stepField_iff]
      exact ⟨fun h => h.2, fun h => ⟨T.parent_closed h, h⟩⟩

noncomputable def Tree.toBranching (T : Tree α) :
    Process α where
  step := fun _ => T.stepField
  initial := fun _ => PUnit.unit.{1}

def RootIndexed.BranchingWalk.genealogicalTree
    {Root : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root)
    (hclosed : IsSiblingClosed (β.step r)) : Tree α where
  carrier := {u | surviveAlong (β.step r) [] u}
  root_mem := by
    change surviveAlong (β.step r) [] []
    exact surviveAlong_nil _ _
  parent_closed := by
    intro u v h
    exact surviveAlong_prefix _ u v h
  sibling_closed := by
    intro u i j hj hij
    change surviveAlong (β.step r) [] (u ++ [j]) at hj
    change surviveAlong (β.step r) [] (u ++ [i])
    rw [surviveAlong_root_append_singleton_iff] at hj ⊢
    exact ⟨hj.1, Step.IsSiblingClosed.survive_of_lt (hclosed u) hij hj.2⟩

theorem Tree.genealogicalTree_toBranching (T : Tree α) :
    ∃ hclosed : IsSiblingClosed
        (T.toBranching.step PUnit.unit.{1}),
      T.toBranching.genealogicalTree PUnit.unit.{1} hclosed = T := by
  let hclosed : IsSiblingClosed (T.toBranching.step PUnit.unit.{1}) := by
    intro u i j hij hi
    by_contra hj
    have hjSurvive : survive (T.stepField u) j :=
      (survive_iff_ne_none _ _).2 hj
    have hjMem : u ++ [j] ∈ T.carrier :=
      (T.survive_stepField_iff u j).1 hjSurvive
    have hiMem := T.sibling_closed hjMem hij
    exact ((survive_iff_ne_none _ _).1
      ((T.survive_stepField_iff u i).2 hiMem)) hi
  refine ⟨hclosed, ?_⟩
  apply Combinatorics.UlamHarris.Tree.ext
  ext u
  change surviveAlong T.stepField [] u ↔ u ∈ T.carrier
  exact T.surviveAlong_stepField_iff u

end Combinatorics.Branching
