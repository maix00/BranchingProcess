import Combinatorics.BranchingWalk.Basic.DisplacementMap

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

/-- The position of an address: start in `Position`, map every edge mark
through `d`, and add the resulting increments. The mark space needs no
algebraic structure. -/
def BranchingWalk.position {Root α Mark Position : Type*}
    [AddCommMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u : TreeNode α) : Position :=
  β.initial r + displaceWith d (β.step r) [] u

@[simp] theorem BranchingWalk.position_id
    {Root α X : Type*} [AddCommMonoid X]
    (β : RootIndexed.BranchingWalk Root α X X)
    (r : Root) (u : TreeNode α) :
    β.position id r u = β.initial r + displace (β.step r) [] u := by
  simp [BranchingWalk.position]

/-- An additive scalar potential may be applied after constructing an
abstract position, or to the initial position and every raw edge mark before
the path is accumulated. -/
theorem BranchingWalk.potential_position
    {Root α Mark Position : Type*} [MeasurableSpace Position]
    [AddCommMonoid Position]
    (φ : AdditivePotential Position) (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u : TreeNode α) :
    φ (β.position d r u) =
      φ (β.initial r) + displaceWith (φ ∘ d) (β.step r) [] u := by
  rw [BranchingWalk.position, φ.map_add, φ.map_displaceWith]

end RootIndexed

end Branching

end Combinatorics
