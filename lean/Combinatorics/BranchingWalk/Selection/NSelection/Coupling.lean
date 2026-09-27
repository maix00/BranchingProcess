import Combinatorics.BranchingWalk.Selection.NSelection.Leftmost

/-!
# One-step comparison with leftmost selection

This file contains the finite counting lemma used by branching-walk
couplings.  Candidate identities and positions are separate: `ι` and `κ`
retain multiplicity, while `position` is used only for threshold comparisons.
No new population order is introduced here.  The conclusion is precisely the
threshold inequality used by `Cloud.RankwiseDominates` and `Cloud.Dominates`.
-/

namespace Combinatorics.Branching.Selection.NSelection

/-- If a retained population is a subpopulation of `source`, has size at most
`N`, and the source threshold counts are bounded by those of `candidates`,
then it is also bounded by the leftmost `N` candidates.  The candidate identity
order only has to refine the position order. -/
theorem filter_card_le_filter_keepFirst
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
        ((keepFirst N rightCandidates).filter fun q => candidatePosition q ≤ a).card := by
  classical
  intro a
  have hleft : (retained.filter fun p => position p ≤ a).card ≤
      (source.filter fun p => position p ≤ a).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hretained)
  have htoCandidates := hleft.trans (hthreshold a)
  have hretainedThreshold :
      (retained.filter fun p => position p ≤ a).card ≤ N :=
    (Finset.card_filter_le _ _).trans hcard
  rw [card_filter_keepFirst_of_downwardClosed N rightCandidates
    (fun q => candidatePosition q ≤ a) (by
      intro p q hp hq hqp hpP
      exact (hmono hp hq hqp).trans hpP)]
  exact le_min hretainedThreshold htoCandidates

end Combinatorics.Branching.Selection.NSelection
