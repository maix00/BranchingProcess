/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Family
public import Combinatorics.BranchingWalk.Basic.Survival.SurviveAlong
public import Combinatorics.BranchingWalk.Basic.Position.DisplacementMap

/-!
# Ancestral paths under whole-family selection

## Public declarations

In `Combinatorics.Branching`:

* `surviveAlong_selectFamily_iff`: a path `v` below `u` survives the selected
  field exactly when it survives the original field and every strict ancestor
  family `field(u ++ v.take j)` is accepted, `j<length v`.
* `displaceWith_selectFamily_eq_of_survive`: on each selected surviving path,
  its displacement under any mark map into an additive monoid equals the
  displacement of the original field.

These are deterministic identities. Whole-family selection preserves each
retained child mark, not merely the number or positions of retained children.
-/

@[expose] public section
namespace Combinatorics.Branching
open Combinatorics.UlamHarris
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem surviveAlong_selectFamily_iff {ι X : Type*}
    (A : Set (Step ι X)) (field : StepField ι X) (u v : TreeNode ι) :
    surviveAlong (fun q => Step.selectFamily A (field q)) u v ↔
      surviveAlong field u v ∧ ∀ j : Fin v.length, field (u ++ v.take j) ∈ A := by
  induction v generalizing u with
  | nil => simp [surviveAlong]
  | cons i v ih =>
    by_cases h : field u ∈ A
    · simp only [surviveAlong, Step.selectFamily_of_mem h, ih,
        List.length_cons, Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ,
        List.take_zero, List.take_succ_cons, List.append_nil, h, true_and]
      simp only [List.append_assoc, List.singleton_append]
      tauto
    · have hno : ¬∀ j : Fin (i :: v).length, field (u ++ (i :: v).take j) ∈ A := by
        intro hall
        exact h (by simpa using hall 0)
      constructor
      · intro hs
        have hfirst := hs.1
        simp [Step.selectFamily_of_notMem h, survive] at hfirst
      · intro hs
        exact False.elim (hno hs.2)

theorem displaceWith_selectFamily_eq_of_survive {ι X Y : Type*} [AddMonoid Y]
    (d : X → Y) (A : Set (Step ι X)) (field : StepField ι X)
    (u v : TreeNode ι)
    (hs : surviveAlong (fun q => Step.selectFamily A (field q)) u v) :
    displaceWith d (fun q => Step.selectFamily A (field q)) u v =
      displaceWith d field u v := by
  induction v generalizing u with
  | nil => rfl
  | cons i v ih =>
    have hroot : field u ∈ A := by
      by_contra h
      have hfirst := hs.1
      simp [Step.selectFamily_of_notMem h, survive] at hfirst
    rw [displaceWith_cons, displaceWith_cons]
    rw [Step.selectFamily_of_mem hroot, ih (u ++ [i]) hs.2]

end Combinatorics.Branching
