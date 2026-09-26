import Probability.BranchingRandomWalk.Population.Candidates.FullRank.Exclusion
import MeasureTheory.BranchingWalk.Step.Ordered

/-!
# Equality of finite and full rank selection

Rank below `N` with respect to every realized child is equivalent to the
finite first-`N`-slot rank, so the selected sets agree. Its lift to the adapted
recursion is in `Candidates/FullSelection.lean`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


/-- Finite-rank selection is not spoiled by omitted late-slot children. -/
theorem finiteLeftmost_mem_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ finiteLeftmost N x ω (multiRootCandidates N s ω)) :
    fullRankBelow N x ω (allMultiRootChildren s ω) q := by
  classical
  let C := multiRootCandidates N s ω
  have hqrank : (earlierCandidates x ω C q).card < N :=
    (Finset.mem_filter.mp hq).2
  intro hex
  obtain ⟨t, htcard, ht⟩ := hex
  by_cases hsubset : t ⊆ C
  · have hsubsetEarlier : t ⊆ earlierCandidates x ω C q := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨hsubset hr, (ht r hr).2⟩
    have hle := Finset.card_le_card hsubsetEarlier
    omega
  · obtain ⟨r, hr, hrnot⟩ := Finset.not_subset.mp hsubset
    have hrq := (ht r hr).2
    obtain ⟨p, hp, j, hj, rfl⟩ := (ht r hr).1
    by_cases hjN : j < N
    · have hmem : childAddress p j ∈ C := by
        unfold C multiRootCandidates
        apply Finset.mem_biUnion.mpr
        refine ⟨p, hp, ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨j, Finset.mem_range.mpr hjN,
          (mem_oneChildCandidate_iff ω p (childAddress p j) j).2
            ⟨hj, rfl⟩⟩
      exact hrnot hmem
    · have hNj : N ≤ j := by omega
      have hlarge := lateChild_earlier_forces_finite_rank
        N x s ω p hp (horder p hp) j hNj hj q hrq
      change N ≤ (earlierCandidates x ω C q).card at hlarge
      omega

/-- A full-process top-`N` child has finite-candidate rank below `N`. -/
theorem fullRankBelow_mem_finiteLeftmost {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ allMultiRootChildren s ω)
    (hrank : fullRankBelow N x ω (allMultiRootChildren s ω) q) :
    q ∈ finiteLeftmost N x ω (multiRootCandidates N s ω) := by
  classical
  have hcandidate := fullRankBelow_child_mem_candidates
    N x s ω horder q hq hrank
  apply Finset.mem_filter.mpr
  refine ⟨hcandidate, ?_⟩
  by_contra hcount
  have hlarge : N ≤
      (earlierCandidates x ω (multiRootCandidates N s ω) q).card := by
    omega
  obtain ⟨t, htSub, htCard⟩ :=
    Finset.exists_subset_card_eq hlarge
  apply hrank
  refine ⟨t, htCard, ?_⟩
  intro r hr
  obtain ⟨hrCandidate, hrEarlier⟩ :=
    Finset.mem_filter.mp (htSub hr)
  exact ⟨multiRootCandidates_subset_all N s ω hrCandidate,
    hrEarlier⟩

/-- The finite first-`N`-slot rank selection agrees exactly with selection
from every realized child of every parent. -/
theorem finiteLeftmost_eq_fullSelection {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealStep (ω p.1 p.2)) :
    (↑(finiteLeftmost N x ω (multiRootCandidates N s ω)) :
      Set (RootAddress m)) =
      {q | q ∈ allMultiRootChildren s ω ∧
        fullRankBelow N x ω (allMultiRootChildren s ω) q} := by
  ext q
  constructor
  · intro hq
    have hq' : q ∈ finiteLeftmost N x ω
        (multiRootCandidates N s ω) := hq
    exact ⟨multiRootCandidates_subset_all N s ω
      ((finiteLeftmost_subset N x ω _) hq'),
      finiteLeftmost_mem_fullRankBelow N x s ω horder q hq'⟩
  · rintro ⟨hq, hrank⟩
    exact fullRankBelow_mem_finiteLeftmost N x s ω horder q hq hrank

end ProbabilityTheory.BranchingRandomWalk
