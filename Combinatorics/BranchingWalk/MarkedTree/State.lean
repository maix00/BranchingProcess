/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.State
public import Combinatorics.BranchingWalk.MarkedTree.OfBranchingWalk

/-!
# State-marked representations of branching walks

## Public declarations

* `Combinatorics.Branching.RootIndexed.BranchingWalk.stateMarkedTree` is the
  realized tree with marks $V(uj)=F(V(u),U(uj))$, $V(\emptyset)=x$,
  for an arbitrary state update $F:S\times E\to S$.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.stateMarkedTree_mark`
  identifies its node mark with `BranchingWalk.state`.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.stateMarkedTree_rootMark`
  identifies its root mark with the supplied initial state.

This construction uses no addition or order on the state space. Sibling
closure is required only for the existing Ulam--Harris tree representation.
-/

@[expose] public section

namespace Combinatorics.Branching.RootIndexed.BranchingWalk

open Combinatorics.UlamHarris

/-- The realized marked tree whose node marks are the recursively updated states. -/
noncomputable def stateMarkedTree {Root α Mark State : Type*} [LT α]
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (hsib : ∀ r, StepField.IsSiblingClosed (β.step r)) :
    UlamHarris.RootIndexed.MarkedTree Root α State :=
  β.markedTreeWith hsib (fun r u _ => β.state F r u)

@[simp] theorem stateMarkedTree_mark {Root α Mark State : Type*} [LT α]
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (hsib : ∀ r, StepField.IsSiblingClosed (β.step r)) (r : Root) (u : TreeNode α)
    (h : u ∈ (β.stateMarkedTree F hsib r).tree.carrier) :
    (β.stateMarkedTree F hsib r).mark u h = β.state F r u := rfl

@[simp] theorem stateMarkedTree_rootMark {Root α Mark State : Type*} [LT α]
    (β : RootIndexed.BranchingWalk Root α Mark State) (F : State → Mark → State)
    (hsib : ∀ r, StepField.IsSiblingClosed (β.step r)) (r : Root) :
    (β.stateMarkedTree F hsib r).rootMark = β.initial r := rfl

end Combinatorics.Branching.RootIndexed.BranchingWalk
