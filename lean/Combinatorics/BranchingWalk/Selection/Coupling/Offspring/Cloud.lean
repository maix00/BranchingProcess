module

public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Finite

/-!
# Cloud-level offspring coupling

This file lifts the finite parent-slot comparison to injective and rankwise
domination of multi-root clouds.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Position Value : Type*}

/-- Shared offspring preserve the lower-tail count comparison.  A source
parent `p` is coupled to `matchParent p`; both use the same slot `i`.  The
target may contain additional parents or slots.  The sole spatial hypothesis
is that advancing the matched target parent by the shared mark lies weakly to
the left of advancing the source parent.

This is the multi-root one-generation core: `Root` is arbitrary, and the map
may match particles belonging to different roots while the child construction
retains the target particle's root. -/
theorem offspringPairs_filter_card_le
    [Preorder Value] [DecidableRel (· ≤ · : Value → Value → Prop)]
    (source target : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (matchParent : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hmatch_mem : ∀ p ∈ source, matchParent p ∈ target)
    (hmatch_inj : Set.InjOn matchParent source)
    (hslot : ∀ p ∈ source, sourceSlots p ⊆ targetSlots (matchParent p))
    (sourceValue targetValue : RootIndexed.TreeNode Root α → α → Value)
    (hle : ∀ p ∈ source, ∀ i ∈ sourceSlots p,
      targetValue (matchParent p) i ≤ sourceValue p i)
    (a : Value) :
    ((offspringPairs source sourceSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        sourceValue pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs target targetSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        targetValue qi.1 qi.2 ≤ a).card := by
  classical
  let pairMatch : RootIndexed.TreeNode Root α × α →
      RootIndexed.TreeNode Root α × α := fun pi => (matchParent pi.1, pi.2)
  apply Finset.card_le_card_of_injOn pairMatch
  · intro pi hpi
    rcases Finset.mem_filter.mp hpi with ⟨hpair, hvalue⟩
    rcases (mem_offspringPairs.mp hpair) with ⟨hp, hi⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_offspringPairs.mpr ⟨hmatch_mem pi.1 hp, hslot pi.1 hp hi⟩,
      (hle pi.1 hp pi.2 hi).trans hvalue⟩
  · intro pi hpi qi hqi heq
    have hp : pi.1 ∈ source :=
      (mem_offspringPairs.mp (Finset.mem_filter.mp hpi).1).1
    have hq : qi.1 ∈ source :=
      (mem_offspringPairs.mp (Finset.mem_filter.mp hqi).1).1
    change (matchParent pi.1, pi.2) = (matchParent qi.1, qi.2) at heq
    obtain ⟨hmatched, hslots⟩ := Prod.ext_iff.mp heq
    have hparents : pi.1 = qi.1 := hmatch_inj hp hq hmatched
    exact Prod.ext hparents hslots

/-- The address-order-free form of one-generation offspring propagation.
An injective spatial matching of multi-root parents, followed by compatible
shared slots, gives the lower-tail comparison of candidate pairs. -/
theorem offspringPairs_filter_card_le_of_injectivelyDominatesBy
    [Preorder Value] [DecidableRel (· ≤ · : Value → Value → Prop)]
    (φ : Position → Value) {Time : Type*}
    {C D : Cloud Time Root α Position} (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (hdom : C.InjectivelyDominatesBy φ D t)
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (sourceValue targetValue : RootIndexed.TreeNode Root α → α → Value)
    (hshared : ∀ p ∈ C.particles t, ∀ q ∈ D.particles t,
      φ (D.position q.1 q.2) ≤ φ (C.position p.1 p.2) →
      ∀ i ∈ sourceSlots p,
        i ∈ targetSlots q ∧ targetValue q i ≤ sourceValue p i)
    (a : Value) :
    ((offspringPairs hCfinite.toFinset sourceSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        sourceValue pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs hDfinite.toFinset targetSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        targetValue qi.1 qi.2 ≤ a).card := by
  classical
  obtain ⟨matchParticle, hmem, hinj, hleft⟩ := hdom
  apply offspringPairs_filter_card_le hCfinite.toFinset hDfinite.toFinset
    sourceSlots targetSlots matchParticle
  · intro p hp
    apply hDfinite.mem_toFinset.mpr
    exact hmem (hCfinite.mem_toFinset.mp hp)
  · intro p hp q hq hpq
    apply hinj (hCfinite.mem_toFinset.mp hp) (hCfinite.mem_toFinset.mp hq) hpq
  · intro p hp i hi
    exact (hshared p (hCfinite.mem_toFinset.mp hp) (matchParticle p)
      (hmem (hCfinite.mem_toFinset.mp hp))
      (hleft p (hCfinite.mem_toFinset.mp hp)) i hi).1
  · intro p hp i hi
    exact (hshared p (hCfinite.mem_toFinset.mp hp) (matchParticle p)
      (hmem (hCfinite.mem_toFinset.mp hp))
      (hleft p (hCfinite.mem_toFinset.mp hp)) i hi).2

/-- Rankwise domination of two finite multi-root parent clouds yields the
lower-tail comparison for their coupled offspring candidates.  The hypothesis
`hshared` states the local fact supplied by the coupling: equal-rank matched
parents expose the same source slots in the target construction, and applying
the same slot keeps the target child weakly to the left.

This theorem composes the two formerly separate steps of the induction:
extracting an injective parent matching and propagating it through one shared
offspring step. -/
theorem offspringPairs_filter_card_le_of_rankwiseDominatesBy
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    [DecidableRel (· ≤ · : Value → Value → Prop)]
    (φ : Position → Value) {Time : Type*}
    {C D : Cloud Time Root α Position} (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (hdom : C.RankwiseDominatesBy φ D t)
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (sourceValue targetValue : RootIndexed.TreeNode Root α → α → Value)
    (hshared : ∀ p ∈ C.particles t, ∀ q ∈ D.particles t,
      (D.mapPosition φ).sliceRank t q = (C.mapPosition φ).sliceRank t p →
      φ (D.position q.1 q.2) ≤ φ (C.position p.1 p.2) →
      ∀ i ∈ sourceSlots p,
        i ∈ targetSlots q ∧ targetValue q i ≤ sourceValue p i)
    (a : Value) :
    ((offspringPairs hCfinite.toFinset sourceSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        sourceValue pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs hDfinite.toFinset targetSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        targetValue qi.1 qi.2 ≤ a).card := by
  classical
  obtain ⟨matchParticle, hmem, hinj, hrank, hleft⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
      φ t hCfinite hdom
  apply offspringPairs_filter_card_le hCfinite.toFinset hDfinite.toFinset
    sourceSlots targetSlots matchParticle
  · intro p hp
    apply hDfinite.mem_toFinset.mpr
    exact hmem (hCfinite.mem_toFinset.mp hp)
  · intro p hp q hq hpq
    apply hinj (hCfinite.mem_toFinset.mp hp) (hCfinite.mem_toFinset.mp hq) hpq
  · intro p hp i hi
    exact (hshared p (hCfinite.mem_toFinset.mp hp) (matchParticle p)
      (hmem (hCfinite.mem_toFinset.mp hp))
      (hrank p (hCfinite.mem_toFinset.mp hp))
      (hleft p (hCfinite.mem_toFinset.mp hp)) i hi).1
  · intro p hp i hi
    exact (hshared p (hCfinite.mem_toFinset.mp hp) (matchParticle p)
      (hmem (hCfinite.mem_toFinset.mp hp))
      (hrank p (hCfinite.mem_toFinset.mp hp))
      (hleft p (hCfinite.mem_toFinset.mp hp)) i hi).2

end Combinatorics.Branching.Selection.Coupling

end
