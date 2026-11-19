/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.BranchingWalk
public import Combinatorics.BranchingWalk.Basic.Position.DisplacementMap

/-!
# State updates along a branching tree

## Public declarations

* `Combinatorics.Branching.stateAlong F β s v p` follows the child marks on
  the path `p` starting at address `v` and state `s`, using the update
  $F:S\times E\to S$. No algebraic structure on either space is required.
* `Combinatorics.Branching.stateAlong_nil` and
  `Combinatorics.Branching.stateAlong_cons` give the recursion equations.
* `Combinatorics.Branching.stateAlong_append` states that following $p++q$
  equals following $q$ from the state and address reached after $p$.
* `Combinatorics.Branching.stateAlong_append_singleton` gives the child
  update, retaining the current state when that child is absent.
* `Combinatorics.Branching.stateAlong_add` specializes to
  $F(s,e)=s+d(e)$: the result is $s+\operatorname{displaceWith}(d,β,v,p)$
  in any additive monoid.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.state` assigns states
  to a walk from its initial states and an update map.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.state_nil` and
  `Combinatorics.Branching.RootIndexed.BranchingWalk.state_append_singleton`
  identify the root state and the child update.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.state_append_singleton_of_eq_some`
  gives $V(uj)=F(V(u),e)$ when the child slot contains `some e`.

Absent child slots leave the state unchanged in this total extension. On a
realized path every slot is present, so each edge applies exactly one update.
The underlying tree and presence predicates are independent of state updates.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Follow marked edges using an arbitrary state update. An absent slot leaves
the state unchanged; the value on unrealized paths is only a total extension. -/
def stateAlong {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v : TreeNode α) : TreeNode α → State
  | [] => s
  | j :: p => stateAlong F β ((β v j).elim s (F s)) (v ++ [j]) p

@[simp] theorem stateAlong_nil {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v : TreeNode α) :
    stateAlong F β s v [] = s := rfl

theorem stateAlong_cons {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v : TreeNode α) (j : α) (p : TreeNode α) :
    stateAlong F β s v (j :: p) =
      stateAlong F β ((β v j).elim s (F s)) (v ++ [j]) p := rfl

/-- State evolution composes when a path is split into two segments. -/
theorem stateAlong_append {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v p q : TreeNode α) :
    stateAlong F β s v (p ++ q) =
      stateAlong F β (stateAlong F β s v p) (v ++ p) q := by
  induction p generalizing s v with
  | nil => simp
  | cons j p ih =>
      simpa [stateAlong, List.append_assoc] using
        ih ((β v j).elim s (F s)) (v ++ [j])

theorem stateAlong_append_singleton {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v p : TreeNode α) (j : α) :
    stateAlong F β s v (p ++ [j]) =
      (β (v ++ p) j).elim (stateAlong F β s v p) (F (stateAlong F β s v p)) := by
  rw [stateAlong_append]
  rfl

/-- Additive displacement is a specialization of general state evolution. -/
theorem stateAlong_add {α Mark State : Type*} [AddMonoid State]
    (d : Mark → State) (β : StepField α Mark) (s : State) (v p : TreeNode α) :
    stateAlong (fun x e => x + d e) β s v p = s + displaceWith d β v p := by
  induction p generalizing s v with
  | nil => simp
  | cons j p ih =>
      simp only [stateAlong_cons, displaceWith, StepField.map_apply, displace_cons]
      rw [ih]
      cases h : β v j <;> simp [Step.map, value', h, add_assoc, displaceWith]

namespace RootIndexed.BranchingWalk

/-- Interpret a branching field in an arbitrary state space. -/
def state {Root α Mark State : Type*} (β : RootIndexed.BranchingWalk Root α Mark State)
    (F : State → Mark → State) (r : Root) (u : TreeNode α) : State :=
  stateAlong F (β.step r) (β.initial r) [] u

@[simp] theorem state_nil {Root α Mark State : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (r : Root) : β.state F r [] = β.initial r := rfl

theorem state_append_singleton {Root α Mark State : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (r : Root) (u : TreeNode α) (j : α) :
    β.state F r (u ++ [j]) = (β.step r u j).elim (β.state F r u) (F (β.state F r u)) := by
  simpa [state] using stateAlong_append_singleton F (β.step r) (β.initial r) [] u j

/-- A present child applies the update to its parent's state. -/
theorem state_append_singleton_of_eq_some {Root α Mark State : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (r : Root) (u : TreeNode α) (j : α) (e : Mark) (h : β.step r u j = some e) :
    β.state F r (u ++ [j]) = F (β.state F r u) e := by
  rw [state_append_singleton, h]
  rfl

end RootIndexed.BranchingWalk

end Combinatorics.Branching
