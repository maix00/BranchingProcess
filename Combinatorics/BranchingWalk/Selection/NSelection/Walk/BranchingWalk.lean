/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.WalkTransform

/-!
# `N`-branching walks and `N`-selections

`NBranchingWalk N α Mark Position` is a branching walk in which every node has
at most `N` surviving children. `NSelection N α Mark Position` is the deterministic selection mechanism
whose image lies in `NBranchingWalk N α X`: from any branching walk it keeps a
sub-walk with at most `N` children per node.

This is the deterministic object. The random `N`-branching walk, a law on
`NBranchingWalk`, and the random `N`-selection live in the probability layer.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Combinatorics

namespace Branching

universe u v

namespace RootIndexed

/-- A root-indexed branching walk in which every node below every root has at
most `N` surviving children. -/
def IsNBranching {Root α Mark Position : Type*} (N : ℕ)
    (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop :=
  ∀ r u, (support (β.step r u)).Finite ∧ (support (β.step r u)).ncard ≤ N

/-- The branching walks in which every node has at most `N` children. -/
abbrev NBranchingWalk (N : ℕ) (Root α Mark Position : Type*) :=
  {β : RootIndexed.BranchingWalk Root α Mark Position // IsNBranching N β}

/-- A deterministic selection mechanism of capacity `N`: its image is an
`N`-branching walk. -/
structure NSelection (N : ℕ) (Root α Mark Position : Type*) [LT α]
    extends RootIndexed.WalkTransform Root α Mark Position where
  /-- The image of every walk has at most `N` children per node. -/
  nbounded : ∀ β, IsNBranching N (select β)

instance (N : ℕ) (Root α Mark Position : Type*) [LT α] :
    CoeFun (NSelection N Root α Mark Position)
      (fun _ => RootIndexed.BranchingWalk Root α Mark Position →
        RootIndexed.BranchingWalk Root α Mark Position) :=
  ⟨fun S => S.select⟩

variable {N : ℕ} {Root α Mark Position : Type*} [LT α]

/-- The image of a walk under an `N`-selection, as an `N`-branching walk. -/
def NSelection.toNBranchingWalk (S : NSelection N Root α Mark Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    NBranchingWalk N Root α Mark Position :=
  ⟨S.select β, S.nbounded β⟩

end RootIndexed

/-- The single-root bounded branching walks. -/
abbrev NBranchingWalk (N : ℕ) (α : Type u)
    (Mark Position : Type v) : Type (max u v) :=
  RootIndexed.NBranchingWalk N PUnit.{1} α Mark Position

/-- A single-root branching-walk selection mechanism of capacity `N`. -/
abbrev NSelection (N : ℕ) (α : Type u)
    (Mark Position : Type v) [LT α] : Type (max u v) :=
  RootIndexed.NSelection N PUnit.{1} α Mark Position

end Branching

end Combinatorics
