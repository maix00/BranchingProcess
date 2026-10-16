/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.StepField

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

def surviveAlong {α X : Type*} (step : StepField α X) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => survive (step v) i ∧
      surviveAlong step (v ++ [i]) p

theorem surviveAlong_nil {α X : Type*} (step : StepField α X)
    (v : TreeNode α) : surviveAlong step v [] := trivial

theorem surviveAlong_cons {α X : Type*} (step : StepField α X)
    (v : TreeNode α) (i : α) (p : TreeNode α) :
    surviveAlong step v (i :: p) ↔
      survive (step v) i ∧ surviveAlong step (v ++ [i]) p := Iff.rfl

theorem surviveAlong_append_singleton {α X : Type*}
    (step : StepField α X) :
    ∀ (v p : TreeNode α) (i : α),
      surviveAlong step v (p ++ [i]) ↔
        surviveAlong step v p ∧ survive (step (v ++ p)) i
  | v, [], i => by simp [surviveAlong]
  | v, j :: p, i => by
      have ih := surviveAlong_append_singleton step (v ++ [j]) p i
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, surviveAlong_cons, hpath]
      rw [ih, and_assoc]

theorem surviveAlong_append {α X : Type*}
    (step : StepField α X) :
    ∀ (v p q : TreeNode α),
      surviveAlong step v (p ++ q) ↔
        surviveAlong step v p ∧ surviveAlong step (v ++ p) q
  | v, [], q => by simp [surviveAlong]
  | v, j :: p, q => by
      have ih := surviveAlong_append step (v ++ [j]) p q
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, surviveAlong_cons, hpath]
      rw [ih, and_assoc]

theorem surviveAlong_rebase {α X : Type*}
    (step : StepField α X) :
    ∀ (u v p : TreeNode α),
      surviveAlong (fun w => step (u ++ w)) v p ↔
        surviveAlong step (u ++ v) p
  | u, v, [] => by simp [surviveAlong]
  | u, v, k :: p => by
      have ih := surviveAlong_rebase step u (v ++ [k]) p
      have hpath : u ++ (v ++ [k]) = (u ++ v) ++ [k] := by simp
      simp only [surviveAlong_cons]
      rw [ih, hpath]

theorem surviveAlong_root_append_singleton_iff
    {α X : Type*} (step : StepField α X) (u : TreeNode α) (i : α) :
    surviveAlong step [] (u ++ [i]) ↔
      surviveAlong step [] u ∧ survive (step u) i := by
  simpa using surviveAlong_append_singleton step [] u i

theorem surviveAlong_root_iff_forall_fin
    {α X : Type*} (step : StepField α X) (u : TreeNode α) :
    surviveAlong step [] u ↔
      ∀ j : Fin u.length, survive (step (u.take j)) (u[j]) := by
  induction u generalizing step with
  | nil => simp [surviveAlong]
  | cons i u ih =>
      simp only [surviveAlong_cons, List.length_cons, Fin.forall_fin_succ]
      constructor
      · rintro ⟨hi, hu⟩
        refine ⟨hi, ?_⟩
        intro j
        have hu' := (surviveAlong_rebase step [i] [] u).2 hu
        simpa [List.take_succ_cons] using
          ((ih (step := fun w => step (i :: w))).mp hu' ⟨j, by omega⟩)
      · rintro ⟨hi, hu⟩
        have hu' : surviveAlong (fun w => step (i :: w)) [] u :=
          (ih (step := fun w => step (i :: w))).mpr ?_
        · refine ⟨hi, (surviveAlong_rebase step [i] [] u).1 hu'⟩
        intro j
        simpa [List.take_succ_cons] using hu j

theorem surviveAlong_prefix
    {α X : Type*} (step : StepField α X)
    (u v : TreeNode α) (h : surviveAlong step [] (u ++ v)) :
    surviveAlong step [] u :=
  (surviveAlong_append step [] u v).mp h |>.1

end Combinatorics.Branching

end
