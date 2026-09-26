import MeasureTheory.BranchingWalk.Selection.Mechanism

/-!
# `N`-branching walks and `N`-selections

`NBranchingWalk N α X` is a branching walk in which every node has at most `N`
present children. `NSelection N α X` is the deterministic selection mechanism
whose image lies in `NBranchingWalk N α X`: from any branching walk it keeps a
sub-walk with at most `N` children per node.

This is the deterministic object. The random `N`-branching walk, a law on
`NBranchingWalk`, and the random `N`-selection live in the probability layer.
-/

namespace MeasureTheory

namespace BranchingWalk

namespace Selection

namespace NSelection

/-- A branching walk in which every node has at most `N` present children. -/
def IsNBranching {α X : Type*} (N : ℕ) (ω : BranchingWalk α X) : Prop :=
  ∀ u, (support (ω u)).Finite ∧ (support (ω u)).ncard ≤ N

/-- The branching walks in which every node has at most `N` children. -/
abbrev NBranchingWalk (N : ℕ) (α X : Type*) :=
  {ω : BranchingWalk α X // IsNBranching N ω}

/-- A deterministic selection mechanism of capacity `N`: its image is an
`N`-branching walk. -/
structure NSelection (N : ℕ) (α X : Type*) extends SelectionMechanism α X where
  /-- The image of every walk has at most `N` children per node. -/
  nbounded : ∀ ω, IsNBranching N (select ω)

instance (N : ℕ) (α X : Type*) :
    CoeFun (NSelection N α X) (fun _ => BranchingWalk α X → BranchingWalk α X) :=
  ⟨fun S => S.select⟩

variable {N : ℕ} {α X : Type*}

/-- The image of a walk under an `N`-selection, as an `N`-branching walk. -/
def toNBranchingWalk (S : NSelection N α X) (ω : BranchingWalk α X) :
    NBranchingWalk N α X :=
  ⟨S.select ω, S.nbounded ω⟩

end NSelection

end Selection

end BranchingWalk

end MeasureTheory
