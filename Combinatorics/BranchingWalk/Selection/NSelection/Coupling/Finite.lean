/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Leftmost

/-!
# One-step comparison with leftmost selection

This file contains the finite counting lemma used by branching-walk
couplings.  Candidate identities and positions are separate: `ι` and `κ`
retain multiplicity, while `position` is used only for threshold comparisons.
No new population order is introduced here.  The conclusion is precisely the
threshold inequality used by `Cloud.RankwiseDominates` and `Cloud.Dominates`.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

/-- If a retained population is a subpopulation of `source`, has size at most
`N`, and the source threshold counts are bounded by those of `candidates`,
then it is also bounded by the leftmost `N` candidates.  The candidate identity
order only has to refine the position order. -/
theorem filter_card_le_filter_selectFirstN
    {ι κ X : Type*} [DecidableEq ι] [LinearOrder κ] [Preorder X]
    [DecidableLE X]
    (N : ℕ) (position : ι → X) (candidatePosition : κ → X)
    (retained source : Finset ι) (rightCandidates : Finset κ)
    (hretained : retained ⊆ source)
    (hcard : retained.card ≤ N)
    (hthreshold : ∀ a : X,
      (source.filter fun p => position p ≤ a).card ≤
        (rightCandidates.filter fun q => candidatePosition q ≤ a).card)
    (hmono : ∀ ⦃p q : κ⦄, p ∈ rightCandidates → q ∈ rightCandidates →
      q ≤ p → candidatePosition q ≤ candidatePosition p) :
    ∀ a : X,
      (retained.filter fun p => position p ≤ a).card ≤
        ((selectFirstN N rightCandidates).filter fun q => candidatePosition q ≤ a).card := by
  classical
  intro a
  have hleft : (retained.filter fun p => position p ≤ a).card ≤
      (source.filter fun p => position p ≤ a).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hretained)
  have htoCandidates := hleft.trans (hthreshold a)
  have hretainedThreshold :
      (retained.filter fun p => position p ≤ a).card ≤ N :=
    (Finset.card_filter_le _ _).trans hcard
  rw [card_filter_selectFirstN_of_downwardClosed N rightCandidates
    (fun q => candidatePosition q ≤ a) (by
      intro p q hp hq hqp hpP
      exact (hmono hp hq hqp).trans hpP)]
  exact le_min hretainedThreshold htoCandidates

/-- Even when the retained population itself has more than `N` particles, any
one retained particle has a leftmost-selected counterpart weakly to its left,
provided `N` is positive. This is the one-point statement used at the overflow
generation, where full population domination is no longer available. -/
theorem exists_selectFirstN_le_of_mem
    {ι κ X : Type*} [DecidableEq ι] [LinearOrder κ] [Preorder X]
    [DecidableLE X]
    (N : ℕ) (hN : 0 < N)
    (position : ι → X) (candidatePosition : κ → X)
    (source : Finset ι) (rightCandidates : Finset κ)
    (hthreshold : ∀ a : X,
      (source.filter fun p => position p ≤ a).card ≤
        (rightCandidates.filter fun q => candidatePosition q ≤ a).card)
    (hmono : ∀ ⦃p q : κ⦄, p ∈ rightCandidates → q ∈ rightCandidates →
      q ≤ p → candidatePosition q ≤ candidatePosition p)
    {p : ι} (hp : p ∈ source) :
    ∃ q ∈ selectFirstN N rightCandidates,
      candidatePosition q ≤ position p := by
  classical
  have hsingleton : ({p} : Finset ι) ⊆ source := by simpa
  have hone : ({p} : Finset ι).card ≤ N := by
    simpa using (Nat.succ_le_iff.mpr hN)
  have hcount := filter_card_le_filter_selectFirstN N position candidatePosition
    {p} source rightCandidates hsingleton hone hthreshold hmono (position p)
  have hleft : (({p} : Finset ι).filter fun r => position r ≤ position p).card = 1 := by
    rw [Finset.filter_singleton]
    simp only [le_refl, ite_true, Finset.card_singleton]
  rw [hleft] at hcount
  have hnonempty :
      ((selectFirstN N rightCandidates).filter fun q =>
        candidatePosition q ≤ position p).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcount)
  obtain ⟨q, hq⟩ := hnonempty
  exact ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩

end Combinatorics.Branching.Selection.NSelection

end
