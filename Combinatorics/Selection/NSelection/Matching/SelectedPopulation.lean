/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.Selection.NSelection.Mechanism.Finite.AtRank
public import Combinatorics.Matching.ThresholdCount

/-!
# Matching into a first-`N` selected population

This file converts threshold-count bounds into injections from objects to
available partners, including injections into a set selected by the
first-`N` rule.

## Public declarations

- `Combinatorics.Selection.NSelection.exists_injective_le_selectFirstNBy`:
  if `objectsToMatch ⊆ objectPopulation`,
  `objectsToMatch.card ≤ N`, and for every order key $a$,
  \[
  \#\{p\in\texttt{objectPopulation}:\texttt{objectOrderKey}(p)\le a\}
  \le
  \#\{q\in\texttt{availablePartners}:\texttt{partnerOrderKey}(q)\le a\},
  \]
  then there is an injective map into
  `selectFirstNBy N partnerOrderKey availablePartners` with
  `partnerOrderKey (f p) ≤ objectOrderKey p`.
- `Combinatorics.Selection.NSelection.exists_injective_le_of_partnerAssignment_into_firstNBy`:
  if an injective assignment $g$ from `objectsToMatch` into
  `availablePartners` satisfies
  `partnerOrderKey (g p) ≤ objectOrderKey p`, then it can be replaced by an
  injective assignment into `selectedPartners` with the same order-key bound,
  whenever `IsFirstNBy N partnerOrderKey availablePartners selectedPartners`.

The generic finite threshold-count matching theorem is
`Combinatorics.Matching.exists_injective_le_of_thresholdCountDomination`. These results
specialize it to capacity-constrained selections and do not depend on the
equal-rank matching map in `NSelection/Matching/ByRank.lean`.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

variable {Object Partner OrderKey : Type*}

/-- A finite `objectsToMatch` set of size at most `N` injects into the first
`N` partners selected from `availablePartners`, provided the threshold counts
of `objectPopulation` are bounded by those of `availablePartners`. -/
theorem exists_injective_le_selectFirstNBy
    [DecidableEq Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (N : ℕ) (objectOrderKey : Object → OrderKey)
    (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch objectPopulation : Finset Object)
    (availablePartners : Finset Partner)
    (hretained : objectsToMatch ⊆ objectPopulation)
    (hcard : objectsToMatch.card ≤ N)
    (hthresholdCount : ∀ a : OrderKey,
      (objectPopulation.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card) :
    ∃ matchedPartner : (p : Object) → p ∈ objectsToMatch → Partner,
      (∀ p hp, matchedPartner p hp ∈ selectFirstNBy N partnerOrderKey availablePartners) ∧
      (∀ p hp, partnerOrderKey (matchedPartner p hp) ≤ objectOrderKey p) ∧
      (∀ p hp q hq, matchedPartner p hp = matchedPartner q hq → p = q) := by
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_thresholdCountDomination
      objectOrderKey partnerOrderKey objectsToMatch (selectFirstNBy N partnerOrderKey availablePartners)
      (filter_card_le_filter_selectFirstNBy N objectOrderKey partnerOrderKey objectsToMatch objectPopulation
        availablePartners hretained hcard hthresholdCount)
  refine ⟨fun p hp => (f ⟨p, hp⟩).1, ?_, ?_, ?_⟩
  · intro p hp
    exact (f ⟨p, hp⟩).2
  · intro p hp
    exact hle ⟨p, hp⟩
  · intro p hp q hq heq
    have hsub : (⟨p, hp⟩ : {p : Object // p ∈ objectsToMatch}) = ⟨q, hq⟩ := by
      apply hinj
      exact Subtype.ext heq
    exact congrArg Subtype.val hsub

/-- A given injective partner assignment from `objectsToMatch` into
`availablePartners` can be restricted to any `selectedPartners` satisfying the
first-`N` property, provided it does not increase order keys. -/
theorem exists_injective_le_of_partnerAssignment_into_firstNBy
    [DecidableEq Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (N : ℕ) (objectOrderKey : Object → OrderKey)
    (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Set Partner)
    (selectedPartners : Finset Partner)
    (hselectedPartners_isFirstNBy :
      IsFirstNBy N partnerOrderKey availablePartners selectedPartners)
    (hobjectsToMatch_card_le_N : objectsToMatch.card ≤ N)
    (partnerAssignment : {p : Object // p ∈ objectsToMatch} → Partner)
    (hpartnerAssignment_mem : ∀ p, partnerAssignment p ∈ availablePartners)
    (hpartnerAssignment_injective : Function.Injective partnerAssignment)
    (hpartnerAssignment_orderKey_le : ∀ p,
      partnerOrderKey (partnerAssignment p) ≤ objectOrderKey p.1) :
    ∃ matchedPartner : (p : Object) → p ∈ objectsToMatch → Partner,
      (∀ p hp, matchedPartner p hp ∈ selectedPartners) ∧
      (∀ p hp, partnerOrderKey (matchedPartner p hp) ≤ objectOrderKey p) ∧
      (∀ p hp q hq, matchedPartner p hp = matchedPartner q hq → p = q) := by
  classical
  let objectsToMatchAttached : Finset {p : Object // p ∈ objectsToMatch} := Finset.univ
  have hobjectsToMatchAttached_card :
      objectsToMatchAttached.card = objectsToMatch.card := by
    simp [objectsToMatchAttached]
  let assignedPartners : Finset Partner :=
    objectsToMatchAttached.image partnerAssignment
  have hassignedPartners_subset : ↑assignedPartners ⊆ availablePartners := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact hpartnerAssignment_mem p
  have hassignedPartners_card : assignedPartners.card = objectsToMatch.card := by
    calc
      assignedPartners.card = objectsToMatchAttached.card := by
        exact Finset.card_image_iff.mpr fun p _ q _ hpq =>
          hpartnerAssignment_injective hpq
      _ = objectsToMatch.card := hobjectsToMatchAttached_card
  have hthresholdCount : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (selectedPartners.filter fun q => partnerOrderKey q ≤ a).card := by
    intro a
    have hattach :
        (objectsToMatchAttached.filter fun p => objectOrderKey p.1 ≤ a).card =
          (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card := by
      have h := congrArg Finset.card
        (Finset.filter_attach (fun p : Object => objectOrderKey p ≤ a) objectsToMatch)
      simpa [objectsToMatchAttached] using h
    have hobjectsToAssignedPartners :
        (objectsToMatchAttached.filter fun p => objectOrderKey p.1 ≤ a).card ≤
          (assignedPartners.filter fun q => partnerOrderKey q ≤ a).card := by
      apply Finset.card_le_card_of_injOn partnerAssignment
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨p, hp'.1, rfl⟩,
          (hpartnerAssignment_orderKey_le p).trans hp'.2⟩
      · intro p _ q _ hpq
        exact hpartnerAssignment_injective hpq
    calc
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card =
          (objectsToMatchAttached.filter fun p => objectOrderKey p.1 ≤ a).card :=
        hattach.symm
      _ ≤ (assignedPartners.filter fun q => partnerOrderKey q ≤ a).card :=
        hobjectsToAssignedPartners
      _ ≤ (selectedPartners.filter fun q => partnerOrderKey q ≤ a).card :=
        filter_card_le_filter_of_isFirstNBy N partnerOrderKey availablePartners
          selectedPartners assignedPartners hselectedPartners_isFirstNBy
          hassignedPartners_subset
          (by rw [hassignedPartners_card]; exact hobjectsToMatch_card_le_N) a
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_thresholdCountDomination
      objectOrderKey partnerOrderKey objectsToMatch selectedPartners hthresholdCount
  refine ⟨fun p hp => (f ⟨p, hp⟩).1, ?_, ?_, ?_⟩
  · intro p hp
    exact (f ⟨p, hp⟩).2
  · intro p hp
    exact hle ⟨p, hp⟩
  · intro p hp q hq heq
    have hsub : (⟨p, hp⟩ : {p : Object // p ∈ objectsToMatch}) = ⟨q, hq⟩ := by
      apply hinj
      exact Subtype.ext heq
    exact congrArg Subtype.val hsub

end Combinatorics.Selection.NSelection
