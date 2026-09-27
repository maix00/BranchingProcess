import Combinatorics.BranchingWalk.Selection.NSelection.Walk

/-!
# The cloud of a deterministic `N`-branching walk

The cloud of a walk is the family of its populations, one finite set of
positions per generation. Because the walk keeps at most `N` particles at each
step, every time slice of the cloud is finite and has at most `N` elements.

Reversing the order on positions reverses the walk, so it reverses the cloud.
The equality `(V.mapOrderDual).cloud = V.cloud.mapOrderDual` says that the cloud
of the reversed walk is the order-dual cloud, which is what makes the leftmost
and rightmost theories a single theory.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

namespace NSelection namespace Walk

variable {X : Type*} [DecidableEq X] {N : ℕ} {M : FiniteNSelection X N}

/-- The generation-`n` slice of the reversed cloud is the order-dual image of
the generation-`n` slice of the cloud. -/
theorem mapOrderDual_points (V : Walk N X M) (n : ℕ) :
    (V.mapOrderDual).cloud.points n = OrderDual.toDual '' V.cloud.points n := by
  show (((V.mapOrderDual).population n : Finset (OrderDual X)) : Set (OrderDual X)) =
    OrderDual.toDual '' ((V.population n : Finset X) : Set X)
  rw [population_mapOrderDual, Finset.coe_image]

/-- Reversing the order of a walk reverses the order of its cloud. -/
theorem mapOrderDual_cloud (V : Walk N X M) :
    (V.mapOrderDual).cloud = V.cloud.mapOrderDual := by
  refine CloudSet.ext fun n q => ?_
  rw [mapOrderDual_points]
  rfl

/-- Membership in the reversed cloud, read back in the original order. -/
@[simp] theorem mem_mapOrderDual_cloud_iff (V : Walk N X M) (n : ℕ)
    (x : X) :
    OrderDual.toDual x ∈ (V.mapOrderDual).cloud.points n ↔ x ∈ V.population n := by
  rw [mapOrderDual_cloud, CloudSet.mem_mapOrderDual_points]
  rfl

end Walk

end NSelection end Selection

end Branching

end Combinatorics
