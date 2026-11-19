/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.MarkedTree.State
public import Combinatorics.UlamHarris.MarkedTree.Measurability
public import MeasureTheory.BranchingWalk.State

/-!
# Measurable realized marked-tree representations

## Public declarations

* `Combinatorics.Branching.surviveAlong_measurableSet` states that presence
  of a fixed finite path is a measurable event in the branching field.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.markedTreeWith_measurable`
  constructs a measurable random marked-tree family from a measurable walk
  and measurable node marks $g(ω,r,u)$. Sibling closure is a shape condition.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.stateMarkedTree_measurable`
  states that the realized state representation $(T,V)$ is measurable for
  every jointly measurable update $F:S\times E\to S$ and measurable walk.

The last theorem concerns the entire marked-tree-valued random object, not
only its fixed-node state coordinates. Neither mark nor state space requires
addition, topology, or a prescribed probability law.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Presence along a fixed path depends measurably on its finitely many slots. -/
theorem surviveAlong_measurableSet {α Mark : Type*} [MeasurableSpace Mark]
    (v p : TreeNode α) : MeasurableSet {β : StepField α Mark | surviveAlong β v p} := by
  induction p generalizing v with
  | nil => exact MeasurableSet.univ
  | cons j p ih =>
      exact ((survive_measurableSet j).preimage (measurable_pi_apply v)).inter
        (ih (v ++ [j]))

namespace RootIndexed.BranchingWalk

/-- Measurable node marks on a measurable realized branching tree give a
measurable marked-tree family. -/
theorem markedTreeWith_measurable {Ω Root α Mark State M : Type*} [LT α]
    [MeasurableSpace Ω] [MeasurableSpace Mark] [MeasurableSpace State] [MeasurableSpace M]
    (β : Ω → RootIndexed.BranchingWalk Root α Mark State) (hβ : Measurable β)
    (hsib : ∀ w r, StepField.IsSiblingClosed ((β w).step r))
    (g : Ω → Root → TreeNode α → M) (hg : ∀ r u, Measurable (fun w => g w r u)) :
    Measurable (fun w => (β w).markedTreeWith (hsib w) (fun r u _ => g w r u)) := by
  have hcoords : Measurable
      (fun b : RootIndexed.BranchingWalk Root α Mark State => (b.step, b.initial)) :=
    Measurable.of_comap_le le_rfl
  have hfield (r : Root) : Measurable (fun w => (β w).step r) :=
    (measurable_pi_apply r).comp (measurable_fst.comp (hcoords.comp hβ))
  have hmem (r : Root) (u : TreeNode α) :
      MeasurableSet {w | surviveAlong ((β w).step r) [] u} :=
    (surviveAlong_measurableSet [] u).preimage (hfield r)
  apply Measurable.of_eval
  intro r
  rw [measurable_comap_iff]
  apply Measurable.prodMk
  · rw [measurable_comap_iff, measurable_set_iff]
    intro u
    exact (measurableSet_setOfPred).1 (hmem r u)
  · apply Measurable.of_eval
    intro u
    classical
    have hm : Measurable
        (Set.piecewise {w | surviveAlong ((β w).step r) [] u}
          (fun w => some (g w r u)) (fun _ => none)) :=
      (measurable_option_some.comp (hg r u)).piecewise (hmem r u) measurable_const
    convert hm using 1
    funext w
    simp only [UlamHarris.MarkedTree.mark?, markedTreeWith, Set.piecewise]
    by_cases h : surviveAlong ((β w).step r) [] u <;> simp [h]

/-- A general measurable update yields a measurable state-marked tree family. -/
theorem stateMarkedTree_measurable {Ω Root α Mark State : Type*} [LT α]
    [MeasurableSpace Ω] [MeasurableSpace Mark] [MeasurableSpace State]
    (β : Ω → RootIndexed.BranchingWalk Root α Mark State) (hβ : Measurable β)
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (hsib : ∀ w r, StepField.IsSiblingClosed ((β w).step r)) :
    Measurable (fun w => (β w).stateMarkedTree F (hsib w)) := by
  exact markedTreeWith_measurable β hβ hsib (fun w r u => (β w).state F r u)
    (fun r u => (state_measurable F hF r u).comp hβ)

end RootIndexed.BranchingWalk

end Combinatorics.Branching
