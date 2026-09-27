import Combinatorics.BranchingWalk.Cloud.Order.Slice
import Mathlib.Data.Finset.Sort

/-!
# The finite layer of the slice order

This is the one layer where the order is stated on a sorted list of positions, the way
the thesis writes it: a slice with finitely many particles is listed particle by particle
in the index order of the cloud, so a position at which several particles sit occurs as
many times as there are particles there, and the order says that the `i`-th position of
the first cloud lies weakly to the left of the `i`-th position of the second one. The
`M(μ₁) ≤ M(μ₂)` clause of the thesis is the statement that every index of the first list
is also an index of the second, i.e. no particle of the first cloud is left over.

The enumeration direction is read off the index order, not fixed by the definition: at
the position-increasing order the list runs from left to right, and at the reversed order
(`OrderDual`, cf. `Cloud.mapOrderDual`) the same particles are listed with reversed
positions, which is the upper-tail form of Bérard–Gouéré. The two sides are mirror
images of one another, never the two clouds exchanged.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- The particles of a finite slice, in increasing index order. -/
noncomputable def Cloud.sortedParticles [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] :
    List (Root × TreeNode α) :=
  (C.particles t).toFinset.sort (· ≤ ·)

/-- The positions of the particles of a finite slice, listed in increasing index order:
one entry per particle, so repeated positions stay repeated. -/
noncomputable def Cloud.sortedPositions [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] : List X :=
  (C.sortedParticles t).map fun p => C.position p.1 p.2

/-- The thesis's finite form of the slice order: `M(C) ≤ M(D)` — every index of the
list of `C` is an index of the list of `D` — and the `i`-th position of `D` lies weakly
to the left of the `i`-th position of `C`. -/
def Cloud.FiniteDominates [LinearOrder (Root × TreeNode α)] [LinearOrder X]
    (C D : Cloud Time Root α X) (t : Time)
    [Fintype (C.particles t)] [Fintype (D.particles t)] : Prop :=
  ∀ i : ℕ, ∀ x : X, (C.sortedPositions t)[i]? = some x →
    ∃ y : X, (D.sortedPositions t)[i]? = some y ∧ y ≤ x

/-- The list has one entry per particle, not one per occupied position. -/
theorem Cloud.length_sortedParticles [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] :
    (C.sortedParticles t).length = Fintype.card (C.particles t) := by
  rw [Cloud.sortedParticles, Finset.length_sort, Set.toFinset_card]

/-- The list of positions has one entry per particle, so a position occupied by several
particles is repeated in the list. -/
theorem Cloud.length_sortedPositions [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] :
    (C.sortedPositions t).length = Fintype.card (C.particles t) := by
  rw [Cloud.sortedPositions, List.length_map, Cloud.length_sortedParticles]

/-- The mirror: reading the positions in the reversed order lists the same particles with
reversed positions, so the `i`-th comparison of `Cloud.FiniteDominates` at the reversed
order is the `i`-th comparison of the upper tail. The particles of `Cloud.mapOrderDual` are
the particles of the cloud, so the two listings only differ in the positions. -/
theorem Cloud.sortedPositions_mapOrderDual [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype ↑(C.particles t)]
    [Fintype ↑((Cloud.mapOrderDual C).particles t)] :
    (Cloud.mapOrderDual C).sortedPositions t =
      (C.sortedPositions t).map OrderDual.toDual := by
  rw [Cloud.sortedPositions, Cloud.sortedPositions, Cloud.sortedParticles,
    Cloud.sortedParticles, List.map_map]
  have h : (C.mapOrderDual.particles t).toFinset = (C.particles t).toFinset :=
    Finset.ext fun p => by
      rw [Set.mem_toFinset, Set.mem_toFinset]
      simp [Cloud.mapOrderDual]
  rw [h]
  congr 1

end Combinatorics.Branching
