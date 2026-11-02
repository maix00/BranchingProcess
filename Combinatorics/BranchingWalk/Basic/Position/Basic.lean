/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.DisplacementMap
public import Combinatorics.BranchingWalk.StepField

/-!
# Positions

## Public declarations

For a root-indexed walk $\beta$, root $r$, address $u$, and mark map $d$, the
position is
$\operatorname{position}_d(\beta,r,u)=\beta.\operatorname{initial}(r)+
\operatorname{displaceWith}(d,\beta.\operatorname{step}(r),[],u)$.
The displacement uses the address-carrying recursion in
`Basic/Position/Displace.lean`, which carries the current address instead of
reconstructing it from a list index.

The public API is:

- `RootIndexed.BranchingWalk.position d β r u` is the initial position at
  root `r` plus the displacement obtained by mapping each edge mark through
  `d` and summing along address `u`.
- `BranchingWalk.position_child` gives the recursion from `u` to `u ++ [i]`,
  and `BranchingWalk.position_id` gives the same-mark additive specialization.
- `BranchingWalk.potential_position` states that an additive potential of
  the position is the potential of the initial point plus the displacement
  formed from the transformed edge marks.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

namespace RootIndexed

/-- The position of an address: start in `Position`, map every edge mark
through `d`, and add the resulting increments. The mark space needs no
algebraic structure. -/
def BranchingWalk.position {Root α Mark Position : Type*}
    [AddMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u : TreeNode α) : Position :=
  β.initial r + displaceWith d (β.step r) [] u

/-- Position recursion at one child.  The increment is read from the mapped
step, so this statement does not require any algebraic structure on the raw
mark type or require an arbitrary mark map to preserve a distinguished zero. -/
theorem BranchingWalk.position_child {Root α Mark Position : Type*}
    [AddMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u : TreeNode α) (i : α) :
    β.position d r (u ++ [i]) =
      β.position d r u + value' ((β.step r u).map d) i := by
  simp only [BranchingWalk.position, displaceWith]
  rw [displace_append_singleton, add_assoc]
  simp only [StepField.map_apply]

@[simp] theorem BranchingWalk.position_id
    {Root α X : Type*} [AddMonoid X]
    (β : RootIndexed.BranchingWalk Root α X X)
    (r : Root) (u : TreeNode α) :
    β.position id r u = β.initial r + displace (β.step r) [] u := by
  simp [BranchingWalk.position]

/-- An additive scalar potential may be applied after constructing an
abstract position, or to the initial position and every raw edge mark before
the path is accumulated. -/
theorem BranchingWalk.potential_position
    {Root α Mark Position : Type*} [MeasurableSpace Position]
    [AddMonoid Position]
    (φ : AdditivePotential Position) (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u : TreeNode α) :
    φ (β.position d r u) =
      φ (β.initial r) + displaceWith (φ ∘ d) (β.step r) [] u := by
  rw [BranchingWalk.position, φ.map_add, φ.map_displaceWith]

end RootIndexed

end Branching

end Combinatorics

end
