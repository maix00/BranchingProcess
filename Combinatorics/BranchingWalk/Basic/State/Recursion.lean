/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.BranchingWalk

/-!
# State evolution along marked paths

## Public declarations

In namespace `Combinatorics.Branching`:

* `stateAlong F β s v p` follows $p$ from address $v$ and state $s$, using
  $F:S\times E\to S$. Absent slots leave its total extension unchanged.
* `stateAlong_nil`, `stateAlong_cons` give the defining recursion.
* `stateAlong_append`, `stateAlong_append_singleton` compose path segments.
* `stateAlong_rebase` identifies recursion below an original prefix with
  recursion in the restricted field.
* `stateAlong?` records absence using the same state recursion;
  `stateAlong?_nil` gives $V_s(v,[])=\operatorname{some}(s)$.
* `stateTree_append_singleton` gives
  $V(uj)=V(u).\mathrm{bind}(x\mapsto U(u,j).\mathrm{map}(F(x,\cdot)))$.
* `stateTree` is its root-based tree representation; `stateTree_root`
  gives $V_s(\varnothing)=s$ and `stateTree_subtree` gives $V_u(v)=V(uv)$
  for surviving $u$.

These definitions require neither addition nor a probability law. Additive
path displacement is defined from this recursion in `Position/Displace.lean`.
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

/-- Rebase an arbitrary state update at a descendant address. -/
theorem stateAlong_rebase {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (u v p : TreeNode α) :
    stateAlong F (fun w ↦ β (u ++ w)) s v p = stateAlong F β s (u ++ v) p := by
  induction p generalizing v s with
  | nil => rfl
  | cons j p ih =>
      simp only [stateAlong_cons]
      rw [ih, List.append_assoc]

/-- Optional observation of the same state-update recursion, recording absence. -/
def stateAlong? {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v p : TreeNode α) : Option State :=
  @ite _ (surviveAlong β v p) (surviveAlong.decidable β v p)
    (some (stateAlong F β s v p)) none

@[simp] theorem stateAlong?_nil {α Mark State : Type*} (F : State → Mark → State)
    (β : StepField α Mark) (s : State) (v : TreeNode α) :
    stateAlong? F β s v [] = some s := by simp [stateAlong?, surviveAlong]

/-- The state at each realized descendant, with `none` at absent addresses. -/
noncomputable def stateTree {α Mark State : Type*} (F : State → Mark → State)
    (s : State) (β : StepField α Mark) : TreeNode α → Option State :=
  fun u ↦ stateAlong? F β s [] u

@[simp] theorem stateTree_root {α Mark State : Type*} (F : State → Mark → State)
    (s : State) (β : StepField α Mark) : stateTree F s β [] = some s := by
  simp [stateTree, stateAlong?, surviveAlong, stateAlong]

/-- The child state is obtained by applying the update to its present parent
and child mark; absence of either gives an absent child. -/
theorem stateTree_append_singleton {α Mark State : Type*} (F : State → Mark → State)
    (s : State) (β : StepField α Mark) (u : TreeNode α) (j : α) :
    stateTree F s β (u ++ [j]) =
      (stateTree F s β u).bind (fun x ↦ (β u j).map (F x)) := by
  classical
  by_cases hu : surviveAlong β [] u
  · cases hj : β u j <;>
      simp [stateTree, stateAlong?, surviveAlong_append_singleton,
        stateAlong_append_singleton, hu, survive, hj]
  · simp [stateTree, stateAlong?, surviveAlong_append_singleton, hu]

/-- A surviving root's state subtree is the original state tree restricted
at that root. No translation or algebraic structure is required. -/
theorem stateTree_subtree {α Mark State : Type*} (F : State → Mark → State)
    (s : State) (β : StepField α Mark) (u v : TreeNode α)
    (hu : surviveAlong β [] u) :
    stateTree F (stateAlong F β s [] u) (fun w ↦ β (u ++ w)) v =
      stateTree F s β (u ++ v) := by
  have hs := surviveAlong_rebase β u [] v
  simp only [List.append_nil] at hs
  have ht := surviveAlong_append β [] u v
  simp only [List.nil_append, hu, true_and] at ht
  by_cases hv : surviveAlong β u v
  · simp only [stateTree, stateAlong?, hs.mpr hv, ht.mpr hv, ite_true]
    rw [stateAlong_rebase, stateAlong_append]
    simp only [List.append_nil, List.nil_append]
  · simp only [stateTree, stateAlong?, mt hs.mp hv, mt ht.mp hv, ite_false]


end Combinatorics.Branching
