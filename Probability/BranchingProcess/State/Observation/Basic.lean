/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Generation
public import Combinatorics.UlamHarris.Relation
public import Mathlib.Data.List.OfFn

/-!
# Node and reproduction observations of the canonical generation process

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `stateAt u x` reads the state `x(|u|,u)` of the node `u` from a generation path.
* `descendantTree u x v = stateAt (u.root,u.address ++ v) x` reads the complete
  descendant tree, including its inherited root state at `v = []`.
* `rootStates x r = stateAt (r,[]) x` reads the initial forest states.
* `offspringStates u x j = stateAt (u.root,u.address ++ [j]) x` reads exactly
  the reproduction observation at the parent `u`.
* `stateAt_ofFn` recovers generation coordinates: `stateAt (r,ofFn v) x = x n (r,v)`.
* `descendantTree_ofFn` reads a finite-tuple root as
  `x(a + |v|, (r, append u v))`.
* `stateAt_measurable`, `descendantTree_measurable`, `rootStates_measurable`,
  and `offspringStates_measurable` prove measurability of these observations.

These maps only read the existing generation process; they introduce no new
state recursion or probability law. In particular the offspring observation
at `u` and the inherited state at `u` are different observations. Their line
information uses `ProbabilityTheory.Tree.linePast` directly.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open Combinatorics.UlamHarris MeasureTheory

variable {Root α S : Type*}

/-- State at a node, read from its own generation. -/
def stateAt (u : RootIndexed.TreeNode Root α)
    (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) : Option S :=
  x u.2.length (u.1, u.2.get)

/-- Complete descendant tree rooted at a specified address. -/
def descendantTree (u : RootIndexed.TreeNode Root α)
    (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) (v : List α) : Option S :=
  stateAt (u.1, u.2 ++ v) x

/-- Joint initial states of all roots. -/
def rootStates (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) (r : Root) : Option S :=
  stateAt (r, []) x

/-- The complete family born to a parent, without revealing the children's reproduction. -/
def offspringStates (u : RootIndexed.TreeNode Root α)
    (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) (j : α) : Option S :=
  stateAt (u.1, u.2 ++ [j]) x

/-- Reading an address encoded by a finite tuple recovers its original generation coordinate. -/
theorem stateAt_ofFn (x : Π n : ℕ, (Root × (Fin n → α)) → Option S)
    (n : ℕ) (p : Root × (Fin n → α)) :
    stateAt (p.1, List.ofFn p.2) x = x n p :=
  congrArg (fun q : Sigma (fun n => Fin n → α) => x q.1 (p.1, q.2))
    (List.equivSigmaTuple.apply_symm_apply ⟨n, p.2⟩)

/-- A finite-tuple root agrees with the existing generation descendant readout. -/
theorem descendantTree_ofFn (x : Π n : ℕ, (Root × (Fin n → α)) → Option S)
    (a : ℕ) (p : Root × (Fin a → α)) (v : List α) :
    descendantTree (p.1, List.ofFn p.2) x v =
      x (a + v.length) (p.1, Fin.append p.2 v.get) := by
  simpa only [List.ofFn_fin_append, List.ofFn_get, descendantTree] using
    stateAt_ofFn x (a + v.length) (p.1, Fin.append p.2 v.get)

variable [MeasurableSpace S]

theorem stateAt_measurable (u : RootIndexed.TreeNode Root α) :
    Measurable (stateAt (S := S) u) := by
  unfold stateAt
  fun_prop

theorem descendantTree_measurable (u : RootIndexed.TreeNode Root α) :
    Measurable (descendantTree (S := S) u) :=
  measurable_pi_iff.mpr fun v => stateAt_measurable (u.1, u.2 ++ v)

theorem rootStates_measurable : Measurable (rootStates (Root := Root) (α := α) (S := S)) :=
  measurable_pi_iff.mpr fun r => stateAt_measurable (r, [])

theorem offspringStates_measurable (u : RootIndexed.TreeNode Root α) :
    Measurable (offspringStates (S := S) u) :=
  measurable_pi_iff.mpr fun j => stateAt_measurable (u.1, u.2 ++ [j])

end ProbabilityTheory.BranchingProcess.State

end
