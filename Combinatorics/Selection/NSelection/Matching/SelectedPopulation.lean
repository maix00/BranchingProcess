/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.Selection.NSelection.Mechanism.Finite.AtRank
public import Combinatorics.Matching.ThresholdCountMatching

/-!
# Matching into a first-`N` selected population

This file converts threshold-count bounds into injections from objects to
available partners, including injections into a set selected by the
first-`N` rule.

## Public declarations

- `Combinatorics.Selection.NSelection.exists_injective_le_selectFirstNBy`:
  a finite `objectsToMatch` set injects into the first-`N` selection from
  `availablePartners` when the threshold counts of its containing
  `objectPopulation` are bounded by those of `availablePartners`.
- `Combinatorics.Selection.NSelection.exists_injective_le_of_embedding_of_isFirstNBy`:
  an injective map from `objectsToMatch` into `availablePartners` that does
  not increase order keys yields an injection into any `selectedPartners`
  satisfying `IsFirstNBy N partnerOrderKey availablePartners selectedPartners`.
- `Combinatorics.Selection.NSelection.exists_injective_le_of_dependent_embedding_of_isFirstNBy`
  gives the same conclusion when the partner map is defined with a membership
  proof for each object.

The generic finite threshold-count matching theorem is
`Combinatorics.Matching.exists_injective_le_of_filter_card_le`. These results
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
    (hthreshold : ∀ a : OrderKey,
      (objectPopulation.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card) :
    ∃ matchedPartner : (p : Object) → p ∈ objectsToMatch → Partner,
      (∀ p hp, matchedPartner p hp ∈ selectFirstNBy N partnerOrderKey availablePartners) ∧
      (∀ p hp, partnerOrderKey (matchedPartner p hp) ≤ objectOrderKey p) ∧
      (∀ p hp q hq, matchedPartner p hp = matchedPartner q hq → p = q) := by
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_filter_card_le
      objectOrderKey partnerOrderKey objectsToMatch (selectFirstNBy N partnerOrderKey availablePartners)
      (filter_card_le_filter_selectFirstNBy N objectOrderKey partnerOrderKey objectsToMatch objectPopulation
        availablePartners hretained hcard hthreshold)
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

/-- Match a finite `objectsToMatch` set into an abstract first-`N` segment of
an arbitrary available-partner set. This set may be uncountable; only
`objectsToMatch` and `selectedPartners` are finite. -/
theorem exists_injective_le_of_embedding_of_isFirstNBy
    [DecidableEq Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (N : ℕ) (objectOrderKey : Object → OrderKey)
    (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Set Partner)
    (selectedPartners : Finset Partner)
    (hselected : IsFirstNBy N partnerOrderKey availablePartners selectedPartners)
    (hcard : objectsToMatch.card ≤ N)
    (partnerOfObject : Object → Partner)
    (hembed_mem : ∀ p ∈ objectsToMatch, partnerOfObject p ∈ availablePartners)
    (hembed_inj : Set.InjOn partnerOfObject ↑objectsToMatch)
    (hembed_le : ∀ p ∈ objectsToMatch,
      partnerOrderKey (partnerOfObject p) ≤ objectOrderKey p) :
    ∃ matchedPartner : (p : Object) → p ∈ objectsToMatch → Partner,
      (∀ p hp, matchedPartner p hp ∈ selectedPartners) ∧
      (∀ p hp, partnerOrderKey (matchedPartner p hp) ≤ objectOrderKey p) ∧
      (∀ p hp q hq, matchedPartner p hp = matchedPartner q hq → p = q) := by
  classical
  let mapped : Finset Partner := objectsToMatch.image partnerOfObject
  have hmappedSubset : ↑mapped ⊆ availablePartners := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hembed_mem p hp
  have hmappedCard : mapped.card = objectsToMatch.card := by
    exact Finset.card_image_iff.mpr fun p hp q hq hpq =>
      hembed_inj hp hq hpq
  have hthreshold : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (selectedPartners.filter fun q => partnerOrderKey q ≤ a).card := by
    intro a
    have hobjectsMapped :
        (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
          (mapped.filter fun q => partnerOrderKey q ≤ a).card := by
      apply Finset.card_le_card_of_injOn partnerOfObject
      · intro p hp
        obtain ⟨hpRetained, hpOrderKey⟩ := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨p, hpRetained, rfl⟩,
          (hembed_le p hpRetained).trans hpOrderKey⟩
      · intro p hp q hq hpq
        exact hembed_inj (Finset.mem_filter.mp hp).1
          (Finset.mem_filter.mp hq).1 hpq
    exact hobjectsMapped.trans
      (filter_card_le_filter_of_isFirstNBy N partnerOrderKey availablePartners
        selectedPartners mapped hselected hmappedSubset
        (by rw [hmappedCard]; exact hcard) a)
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_filter_card_le
      objectOrderKey partnerOrderKey objectsToMatch selectedPartners hthreshold
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

/-- Dependent-witness form of the preceding theorem. It is convenient when the
partner map is defined only after proving that an object belongs to
`objectsToMatch`. -/
theorem exists_injective_le_of_dependent_embedding_of_isFirstNBy
    [DecidableEq Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (N : ℕ) (objectOrderKey : Object → OrderKey)
    (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Set Partner)
    (selectedPartners : Finset Partner)
    (hselected : IsFirstNBy N partnerOrderKey availablePartners selectedPartners)
    (hcard : objectsToMatch.card ≤ N)
    (partnerOfObject : (p : Object) → p ∈ objectsToMatch → Partner)
    (hembed_mem : ∀ p hp, partnerOfObject p hp ∈ availablePartners)
    (hembed_inj : ∀ p hp q hq, partnerOfObject p hp = partnerOfObject q hq → p = q)
    (hembed_le : ∀ p hp,
      partnerOrderKey (partnerOfObject p hp) ≤ objectOrderKey p) :
    ∃ matchedPartner : (p : Object) → p ∈ objectsToMatch → Partner,
      (∀ p hp, matchedPartner p hp ∈ selectedPartners) ∧
      (∀ p hp, partnerOrderKey (matchedPartner p hp) ≤ objectOrderKey p) ∧
      (∀ p hp q hq, matchedPartner p hp = matchedPartner q hq → p = q) := by
  classical
  let attached : Finset {p : Object // p ∈ objectsToMatch} := Finset.univ
  have hattachedCard : attached.card = objectsToMatch.card := by
    simp [attached]
  obtain ⟨matchAttached, hmem, hle, hinj⟩ :=
    exists_injective_le_of_embedding_of_isFirstNBy N
      (fun p : {p : Object // p ∈ objectsToMatch} => objectOrderKey p.1)
      partnerOrderKey attached availablePartners selectedPartners hselected
      (by rw [hattachedCard]; exact hcard)
      (fun p => partnerOfObject p.1 p.2)
      (by intro p _; exact hembed_mem p.1 p.2)
      (by
        intro p _ q _ hpq
        exact Subtype.ext (hembed_inj p.1 p.2 q.1 q.2 hpq))
      (by intro p _; exact hembed_le p.1 p.2)
  exact ⟨fun p hp => matchAttached ⟨p, hp⟩ (Finset.mem_univ _),
    (fun p hp => hmem ⟨p, hp⟩ (Finset.mem_univ _)),
    (fun p hp => hle ⟨p, hp⟩ (Finset.mem_univ _)),
    fun p hp q hq hpq => congrArg Subtype.val
      (hinj ⟨p, hp⟩ (Finset.mem_univ _) ⟨q, hq⟩ (Finset.mem_univ _) hpq)⟩
end Combinatorics.Selection.NSelection
