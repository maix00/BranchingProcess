import Probability.BranchingRandomWalk.Population.Candidates.FullRank.Definition
import MeasureTheory.BranchingWalk.Step.Ordered.Basic

/-!
# Late slots cannot improve a finite rank

A child at slot `j ≥ N` that is ahead of `q` already forces `N` strictly
earlier candidates ahead of `q`, all of which lie in the finite first-`N`-slot
candidate set. Hence entire-sets rank comparison needs no slot cutoff.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


/-- Every full-process child whose strict rank is below `N` belongs to the
finite first-`N`-slots candidate set. -/
theorem fullRankBelow_child_mem_candidates {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ allMultiRootChildren s ω)
    (hrank : fullRankBelow N x ω (allMultiRootChildren s ω) q) :
    q ∈ multiRootCandidates N s ω := by
  obtain ⟨p, hp, j, hj, rfl⟩ := hq
  by_cases hjN : j < N
  · unfold multiRootCandidates
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr hjN, ?_⟩
    simp [oneChildCandidate, hj]
  · have hNj : N ≤ j := by omega
    exact (lateChild_not_fullRankBelow N x s ω p hp
      (horder p hp) j hNj hj) hrank |>.elim

/-- If a late-slot child is ahead of `q`, its `N` earlier siblings are
already among the finite candidates and all ahead of `q`. -/
theorem lateChild_earlier_forces_finite_rank {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootStepField m ℝ)
    (p : RootAddress m) (hp : p ∈ s)
    (horder : OrderedNatRealStep (ω p.1 p.2))
    (j : ℕ) (hNj : N ≤ j)
    (hj : present (ω p.1 p.2) j)
    (q : RootAddress m)
    (hjq : candidateEarlier x ω (childAddress p j) q) :
    N ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card := by
  classical
  let t : Finset (RootAddress m) :=
    (Finset.range N).image (childAddress p)
  have htcard : t.card = N := by
    dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  have hsubset : t ⊆
      earlierCandidates x ω (multiRootCandidates N s ω) q := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : present (ω p.1 p.2) i :=
      orderedNatStep_support_initial
        (ω p.1 p.2) horder hij hj
    have hcandidate : childAddress p i ∈ multiRootCandidates N s ω := by
      unfold multiRootCandidates
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hp, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, ?_⟩
      exact (mem_oneChildCandidate_iff ω p (childAddress p i) i).2
        ⟨hreal, rfl⟩
    have hleft := candidateEarlier_ordered_siblings
      x ω p horder hij hj
    have hright : candidateEarlier x ω (childAddress p i) q :=
      (candidateEarlier_iff_key_lt x ω _ _).2
        (lt_trans
          ((candidateEarlier_iff_key_lt x ω _ _).1 hleft)
          ((candidateEarlier_iff_key_lt x ω _ _).1 hjq))
    exact Finset.mem_filter.mpr ⟨hcandidate, hright⟩
  calc
    N = t.card := htcard.symm
    _ ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card :=
      Finset.card_le_card hsubset

end ProbabilityTheory.BranchingRandomWalk
