import Combinatorics.UlamHarris.Basic

/-!
# Declared splits of a marked tree

`splitDeclaration path splitMark` declares a split at generation `n + 1`
whenever the mark at the parent `path n` lies in `splitMark`; generation zero
never declares a split. The first declared split generation is proved to be a
stopping time for the generation filtration in
`Probability/BranchingRandomWalk/Timing/DeclaredSplit.lean`.
-/

namespace Combinatorics

namespace UlamHarris

variable {α : Type*} {M : Type*}

/-- The split is declared when the child mark at the parent has been
revealed. Generation zero cannot declare a split. -/
def splitDeclaration (path : ℕ → Mark α M → TreeNode α)
    (splitMark : Set M) : ℕ → Set (Mark α M)
  | 0 => ∅
  | n + 1 => {ω | ω (path n ω) ∈ splitMark}

end UlamHarris

end Combinatorics
