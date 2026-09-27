import Combinatorics.BranchingWalk.Selection.Mechanism

set_option linter.dupNamespace false

/-!
# `N`-branching walks and `N`-selections

`NBranchingWalk N α X` is a branching walk in which every node has at most `N`
survive children. `NSelection N α X` is the deterministic selection mechanism
whose image lies in `NBranchingWalk N α X`: from any branching walk it keeps a
sub-walk with at most `N` children per node.

This is the deterministic object. The random `N`-branching walk, a law on
`NBranchingWalk`, and the random `N`-selection live in the probability layer.
-/

namespace Combinatorics

namespace Branching

universe u v

namespace RootIndexed

/-- A root-indexed branching walk in which every node below every root has at
most `N` surviving children. -/
def IsNBranching {Root α X : Type*} (N : ℕ)
    (β : RootIndexed.BranchingWalk Root α X X) : Prop :=
  ∀ r u, (support (β.step r u)).Finite ∧ (support (β.step r u)).ncard ≤ N

/-- The branching walks in which every node has at most `N` children. -/
abbrev NBranchingWalk (N : ℕ) (Root α X : Type*) :=
  {β : RootIndexed.BranchingWalk Root α X X // IsNBranching N β}

/-- A deterministic selection mechanism of capacity `N`: its image is an
`N`-branching walk. -/
structure NSelection (N : ℕ) (Root α X : Type*) [LT α]
    extends RootIndexed.SelectionMechanism Root α X where
  /-- The image of every walk has at most `N` children per node. -/
  nbounded : ∀ β, IsNBranching N (select β)

instance (N : ℕ) (Root α X : Type*) [LT α] :
    CoeFun (NSelection N Root α X)
      (fun _ => RootIndexed.BranchingWalk Root α X X → RootIndexed.BranchingWalk Root α X X) :=
  ⟨fun S => S.select⟩

variable {N : ℕ} {Root α X : Type*} [LT α]

/-- The image of a walk under an `N`-selection, as an `N`-branching walk. -/
def NSelection.toNBranchingWalk (S : NSelection N Root α X)
    (β : RootIndexed.BranchingWalk Root α X X) :
    NBranchingWalk N Root α X :=
  ⟨S.select β, S.nbounded β⟩

end RootIndexed

/-- The single-root bounded branching walks. -/
abbrev NBranchingWalk (N : ℕ) (α : Type u) (X : Type v) : Type (max u v) :=
  RootIndexed.NBranchingWalk N PUnit.{1} α X

/-- A single-root branching-walk selection mechanism of capacity `N`. -/
abbrev NSelection (N : ℕ) (α : Type u) (X : Type v) [LT α] : Type (max u v) :=
  RootIndexed.NSelection N PUnit.{1} α X

/-- The single-root and `PUnit`-root-indexed bounded mechanisms are identical. -/
def nSelectionEquiv (N : ℕ) (α : Type u) (X : Type v) [LT α] :
    NSelection N α X ≃ RootIndexed.NSelection N PUnit.{1} α X :=
  Equiv.refl _

end Branching

end Combinatorics
