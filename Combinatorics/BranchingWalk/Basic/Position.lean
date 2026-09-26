import Combinatorics.BranchingWalk.Basic.Displace

/-!
# Positions

The position of an address in a walk is the initial position of its root plus
the displacement along the address, so it is read off the walk's own data:
`RootIndexed.BranchingWalk.position β r u`. The displacement itself is the
address-carrying recursion of `Basic/Displace.lean`, which carries the current
address instead of reconstructing it from a list index.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

namespace RootIndexed

/-- The position of an address in a walk: the initial position of its root plus
the displacement from the root to that address. -/
def BranchingWalk.position {Root α X : Type*} [AddCommMonoid X]
    (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α) : X :=
  β.initial r + displace (β.step r) [] u

end RootIndexed

end Branching

end Combinatorics
