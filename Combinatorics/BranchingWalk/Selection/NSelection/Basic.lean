import Combinatorics.BranchingWalk.Selection.Mechanism

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

namespace Selection

namespace NSelection

/-- A branching walk in which every node has at most `N` survive children. -/
def IsNBranching {α X : Type*} (N : ℕ) (β : BranchingWalk α X) : Prop :=
  ∀ u, (support (β.step () u)).Finite ∧ (support (β.step () u)).ncard ≤ N

/-- The branching walks in which every node has at most `N` children. -/
abbrev NBranchingWalk (N : ℕ) (α X : Type*) :=
  {β : BranchingWalk α X // IsNBranching N β}

/-- A deterministic selection mechanism of capacity `N`: its image is an
`N`-branching walk. -/
structure NSelection (N : ℕ) (α X : Type*) [LT α] extends SelectionMechanism α X where
  /-- The image of every walk has at most `N` children per node. -/
  nbounded : ∀ β, IsNBranching N (select β)

instance (N : ℕ) (α X : Type*) [LT α] :
    CoeFun (NSelection N α X) (fun _ => BranchingWalk α X → BranchingWalk α X) :=
  ⟨fun S => S.select⟩

variable {N : ℕ} {α X : Type*} [LT α]

/-- The image of a walk under an `N`-selection, as an `N`-branching walk. -/
def toNBranchingWalk (S : NSelection N α X) (β : BranchingWalk α X) :
    NBranchingWalk N α X :=
  ⟨S.select β, S.nbounded β⟩

end NSelection

end Selection

end Branching

end Combinatorics
