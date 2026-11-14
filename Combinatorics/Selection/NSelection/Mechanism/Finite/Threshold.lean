/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Finite.Leftmost

/-!
# Threshold-count bounds for first-N selection

For finite sets of objects and available partners, let `objectsToMatch` be a
subset of `objectPopulation` with at most \(N\) elements. If every threshold
count of `objectPopulation` is bounded by the corresponding count in
`availablePartners`, and the partner order key is monotone in the label order,
then the first-\(N\) selected partners dominate every threshold count of
`objectsToMatch`. When \(N>0\), each object in `objectPopulation` also has a
selected partner whose order key is no larger than the object's key.

The public declarations are `filter_card_le_filter_selectFirstN` for the
threshold-count inequality and `exists_selectFirstN_le_of_mem` for the
one-object consequence. The two sets may use different label types; the keys
provide the comparison between them.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

/-- If `objectsToMatch` is a subpopulation of `objectPopulation`, has size at
most `N`, and every threshold count of `objectPopulation` is bounded by the
corresponding count in `availablePartners`, then its threshold counts are
bounded by those of the first-`N` selected partners. The partner label order
need only refine `partnerOrderKey`. -/
theorem filter_card_le_filter_selectFirstN
    {ι κ X : Type*} [DecidableEq ι] [LinearOrder κ] [Preorder X]
    [DecidableLE X]
    (N : ℕ) (objectOrderKey : ι → X) (partnerOrderKey : κ → X)
    (objectsToMatch objectPopulation : Finset ι) (availablePartners : Finset κ)
    (hobjectsToMatch_subset_objectPopulation : objectsToMatch ⊆ objectPopulation)
    (hobjectsToMatch_card_le_N : objectsToMatch.card ≤ N)
    (hobjectPopulation_thresholdCount_le_availablePartner_thresholdCount : ∀ a : X,
      (objectPopulation.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card)
    (hpartnerOrderKey_mono : ∀ ⦃p q : κ⦄, p ∈ availablePartners → q ∈ availablePartners →
      q ≤ p → partnerOrderKey q ≤ partnerOrderKey p) :
    ∀ a : X,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        ((selectFirstN N availablePartners).filter fun q => partnerOrderKey q ≤ a).card := by
  classical
  intro a
  have hleft : (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
      (objectPopulation.filter fun p => objectOrderKey p ≤ a).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hobjectsToMatch_subset_objectPopulation)
  have htoCandidates := hleft.trans
    (hobjectPopulation_thresholdCount_le_availablePartner_thresholdCount a)
  have hobjectsToMatch_thresholdCount_le_N :
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤ N :=
    (Finset.card_filter_le _ _).trans hobjectsToMatch_card_le_N
  rw [card_filter_selectFirstN_of_downwardClosed N availablePartners
    (fun q => partnerOrderKey q ≤ a) (by
      intro p q hp hq hqp hpP
      exact (hpartnerOrderKey_mono hp hq hqp).trans hpP)]
  exact le_min hobjectsToMatch_thresholdCount_le_N htoCandidates

/-- For positive `N`, every object in `objectPopulation` has a partner among
the first-`N` selected partners whose order key is no larger. -/
theorem exists_selectFirstN_le_of_mem
    {ι κ X : Type*} [DecidableEq ι] [LinearOrder κ] [Preorder X]
    [DecidableLE X]
    (N : ℕ) (hN : 0 < N)
    (objectOrderKey : ι → X) (partnerOrderKey : κ → X)
    (objectPopulation : Finset ι) (availablePartners : Finset κ)
    (hobjectPopulation_thresholdCount_le_availablePartner_thresholdCount : ∀ a : X,
      (objectPopulation.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card)
    (hpartnerOrderKey_mono : ∀ ⦃p q : κ⦄, p ∈ availablePartners → q ∈ availablePartners →
      q ≤ p → partnerOrderKey q ≤ partnerOrderKey p)
    {p : ι} (hp : p ∈ objectPopulation) :
    ∃ q ∈ selectFirstN N availablePartners,
      partnerOrderKey q ≤ objectOrderKey p := by
  classical
  have hsingleton : ({p} : Finset ι) ⊆ objectPopulation := by simpa
  have hone : ({p} : Finset ι).card ≤ N := by
    simpa using (Nat.succ_le_iff.mpr hN)
  have hcount := filter_card_le_filter_selectFirstN N objectOrderKey
    partnerOrderKey {p} objectPopulation availablePartners hsingleton hone
    hobjectPopulation_thresholdCount_le_availablePartner_thresholdCount
    hpartnerOrderKey_mono (objectOrderKey p)
  have hleft : (({p} : Finset ι).filter fun r => objectOrderKey r ≤ objectOrderKey p).card = 1 := by
    rw [Finset.filter_singleton]
    simp only [le_refl, ite_true, Finset.card_singleton]
  rw [hleft] at hcount
  have hnonempty :
      ((selectFirstN N availablePartners).filter fun q =>
        partnerOrderKey q ≤ objectOrderKey p).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcount)
  obtain ⟨q, hq⟩ := hnonempty
  exact ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩

end Combinatorics.Selection.NSelection

end
