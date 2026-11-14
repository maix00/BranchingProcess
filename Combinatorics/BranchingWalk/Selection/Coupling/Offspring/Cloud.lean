/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Finite

/-!
# Cloud-level offspring coupling

This file lifts the finite parent-slot comparison to injective and rankwise
domination of multi-root clouds.

## Public declarations

For each threshold \(a\), an injective parent match with compatible offspring
slots and no larger partner-child order keys gives the lower-tail comparison
\[
\bigl|\{(p,i)\in P_C:\psi_C(p,i)\le a\}\bigr|
\le
\bigl|\{(q,i)\in P_D:\psi_D(q,i)\le a\}\bigr|.
\]
The same inequality follows when the parent populations are related by
injective or rankwise spatial domination.

* `Combinatorics.Branching.Selection.Coupling.offspringPairs_filter_card_le`
  compares the cardinalities of the object-population and partner-population parent-slot pairs whose
  values are at most `a`, assuming an injective parent match, compatible slots,
  and `partnerChildOrderKey (matchParent p) i ≤ objectChildOrderKey p i`.
* `Combinatorics.Branching.Selection.Coupling.offspringPairs_filter_card_le_of_injectivelyDominatesBy`
  obtains that comparison from injective domination of finite multi-root
  clouds and a shared-slot value comparison.
* `Combinatorics.Branching.Selection.Coupling.offspringPairs_filter_card_le_of_rankwiseDominatesBy`
  obtains the same comparison from rankwise domination and a shared-slot
  value comparison for matched ranks.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Position Value : Type*}

/-- Shared offspring preserve the lower-tail count comparison.  An object
parent `p` is coupled to `matchParent p`; both use the same slot `i`.  The
partner population may contain additional parents or slots. The spatial
hypothesis compares the positions after applying that shared mark.

This is the multi-root one-generation core: `Root` is arbitrary, and the map
may match particles belonging to different roots while the child construction
retains the partner particle's root. -/
theorem offspringPairs_filter_card_le
    [Preorder Value] [DecidableRel (· ≤ · : Value → Value → Prop)]
    (objectsToMatch availablePartners : Finset (RootIndexed.TreeNode Root α))
    (objectSlots partnerSlots : RootIndexed.TreeNode Root α → Finset α)
    (matchParent : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hmatch_mem : ∀ p ∈ objectsToMatch, matchParent p ∈ availablePartners)
    (hmatch_inj : Set.InjOn matchParent objectsToMatch)
    (hslot : ∀ p ∈ objectsToMatch, objectSlots p ⊆ partnerSlots (matchParent p))
    (objectChildOrderKey partnerChildOrderKey : RootIndexed.TreeNode Root α → α → Value)
    (hle : ∀ p ∈ objectsToMatch, ∀ i ∈ objectSlots p,
      partnerChildOrderKey (matchParent p) i ≤ objectChildOrderKey p i)
    (a : Value) :
    ((offspringPairs objectsToMatch objectSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        objectChildOrderKey pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs availablePartners partnerSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        partnerChildOrderKey qi.1 qi.2 ≤ a).card := by
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
    have hp : pi.1 ∈ objectsToMatch :=
      (mem_offspringPairs.mp (Finset.mem_filter.mp hpi).1).1
    have hq : qi.1 ∈ objectsToMatch :=
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
    {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hobjectsToMatchFinite : (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : (availablePartnersCloud.particles t).Finite)
    (hdom : objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t)
    (objectSlots partnerSlots : RootIndexed.TreeNode Root α → Finset α)
    (objectChildOrderKey partnerChildOrderKey : RootIndexed.TreeNode Root α → α → Value)
    (hshared : ∀ p ∈ objectsToMatchCloud.particles t, ∀ q ∈ availablePartnersCloud.particles t,
      φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2) →
      ∀ i ∈ objectSlots p,
        i ∈ partnerSlots q ∧ partnerChildOrderKey q i ≤ objectChildOrderKey p i)
    (a : Value) :
    ((offspringPairs hobjectsToMatchFinite.toFinset objectSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        objectChildOrderKey pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs havailablePartnersFinite.toFinset partnerSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        partnerChildOrderKey qi.1 qi.2 ≤ a).card := by
  classical
  obtain ⟨partnerOfObject, hmem, hinj, hleft⟩ := hdom
  apply offspringPairs_filter_card_le hobjectsToMatchFinite.toFinset havailablePartnersFinite.toFinset
    objectSlots partnerSlots partnerOfObject
  · intro p hp
    apply havailablePartnersFinite.mem_toFinset.mpr
    exact hmem (hobjectsToMatchFinite.mem_toFinset.mp hp)
  · intro p hp q hq hpq
    apply hinj (hobjectsToMatchFinite.mem_toFinset.mp hp) (hobjectsToMatchFinite.mem_toFinset.mp hq) hpq
  · intro p hp i hi
    exact (hshared p (hobjectsToMatchFinite.mem_toFinset.mp hp) (partnerOfObject p)
      (hmem (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hleft p (hobjectsToMatchFinite.mem_toFinset.mp hp)) i hi).1
  · intro p hp i hi
    exact (hshared p (hobjectsToMatchFinite.mem_toFinset.mp hp) (partnerOfObject p)
      (hmem (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hleft p (hobjectsToMatchFinite.mem_toFinset.mp hp)) i hi).2

/-- Rankwise domination of two finite multi-root parent clouds yields the
lower-tail comparison for their coupled offspring candidates.  The hypothesis
`hshared` states the local fact supplied by the coupling: equal-rank matched
parents expose the same object slots in the partner construction, and applying
the same slot keeps the partner child weakly to the left.

This theorem composes the two formerly separate steps of the induction:
extracting an injective parent matching and propagating it through one shared
offspring step. -/
theorem offspringPairs_filter_card_le_of_rankwiseDominatesBy
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    [DecidableRel (· ≤ · : Value → Value → Prop)]
    (φ : Position → Value) {Time : Type*}
    {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hobjectsToMatchFinite : (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : (availablePartnersCloud.particles t).Finite)
    (hdom : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t)
    (objectSlots partnerSlots : RootIndexed.TreeNode Root α → Finset α)
    (objectChildOrderKey partnerChildOrderKey : RootIndexed.TreeNode Root α → α → Value)
    (hshared : ∀ p ∈ objectsToMatchCloud.particles t, ∀ q ∈ availablePartnersCloud.particles t,
      (availablePartnersCloud.mapPosition φ).sliceRank t q = (objectsToMatchCloud.mapPosition φ).sliceRank t p →
      φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2) →
      ∀ i ∈ objectSlots p,
        i ∈ partnerSlots q ∧ partnerChildOrderKey q i ≤ objectChildOrderKey p i)
    (a : Value) :
    ((offspringPairs hobjectsToMatchFinite.toFinset objectSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        objectChildOrderKey pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs havailablePartnersFinite.toFinset partnerSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        partnerChildOrderKey qi.1 qi.2 ≤ a).card := by
  classical
  obtain ⟨partnerOfObject, hmem, hinj, hrank, hleft⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
      φ t hobjectsToMatchFinite hdom
  apply offspringPairs_filter_card_le hobjectsToMatchFinite.toFinset havailablePartnersFinite.toFinset
    objectSlots partnerSlots partnerOfObject
  · intro p hp
    apply havailablePartnersFinite.mem_toFinset.mpr
    exact hmem (hobjectsToMatchFinite.mem_toFinset.mp hp)
  · intro p hp q hq hpq
    apply hinj (hobjectsToMatchFinite.mem_toFinset.mp hp) (hobjectsToMatchFinite.mem_toFinset.mp hq) hpq
  · intro p hp i hi
    exact (hshared p (hobjectsToMatchFinite.mem_toFinset.mp hp) (partnerOfObject p)
      (hmem (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hrank p (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hleft p (hobjectsToMatchFinite.mem_toFinset.mp hp)) i hi).1
  · intro p hp i hi
    exact (hshared p (hobjectsToMatchFinite.mem_toFinset.mp hp) (partnerOfObject p)
      (hmem (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hrank p (hobjectsToMatchFinite.mem_toFinset.mp hp))
      (hleft p (hobjectsToMatchFinite.mem_toFinset.mp hp)) i hi).2

end Combinatorics.Branching.Selection.Coupling

end
