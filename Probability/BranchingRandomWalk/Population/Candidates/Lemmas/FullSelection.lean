/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Combinatorics.BranchingWalk.Step.Ordering.Monotone
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
import Probability.BranchingRandomWalk.Population.Candidates.FullChildren
import Probability.BranchingRandomWalk.Population.Candidates.Leftmost
import Probability.BranchingRandomWalk.Population.Candidates.MultiRoot
import Probability.BranchingRandomWalk.Population.Processes.Selected.Basic

/-!
# Finite-prefix comparison lemmas for full selection

These non-reusable declarations form the proof chain comparing a finite
first-$N$-slot candidate set with selection from all realized children. The
abstract first-$N$ selection specifications live in
`Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic`; this file
proves the additional branching-specific fact that ordered siblings beyond
the finite slot cutoff cannot enter the selected set.

## Internal proof declarations

- `ProbabilityTheory.BranchingRandomWalk.multiRootCandidates_subset_all`
  embeds the finite first-$N$-slot candidates into all realized children.
- `ProbabilityTheory.BranchingRandomWalk.childAddress_injective` states that
  $j\mapsto\operatorname{RootIndexed.childAddress}(p,j)$ is injective.
- `ProbabilityTheory.BranchingRandomWalk.lateChild_not_fullRankBelow` and
  `ProbabilityTheory.BranchingRandomWalk.lateChild_earlier_forces_finite_rank`
  use ordered offspring to show that a realized child at slot $j\ge N$ has
  $N$ earlier siblings, so it cannot enter the first $N$.
- `ProbabilityTheory.BranchingRandomWalk.fullRankBelow_child_mem_candidates`
  places every selected full child in the finite candidate set.
- `ProbabilityTheory.BranchingRandomWalk.finiteLeftmost_mem_fullRankBelow`,
  `ProbabilityTheory.BranchingRandomWalk.fullRankBelow_mem_finiteLeftmost`,
  and `ProbabilityTheory.BranchingRandomWalk.finiteLeftmost_eq_fullSelection`
  prove equality of the finite-slot and full-child selections.
-/

open MeasureTheory

section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

lemma multiRootCandidates_subset_all {m : ℕ}
    (N : ℕ) (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ) :
    ↑(multiRootCandidates N s ω) ⊆ allMultiRootChildren s ω := by
  intro q hq
  unfold multiRootCandidates at hq
  obtain ⟨p, hp, hq'⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨j, _, hqj⟩ := Finset.mem_biUnion.mp hq'
  obtain ⟨hj, rfl⟩ :=
    (mem_oneChildCandidate_iff ω p q j).1 hqj
  exact ⟨p, hp, j, hj, rfl⟩

lemma childAddress_injective {m : ℕ} (p : RootAddress m ℕ) :
    Function.Injective (RootIndexed.childAddress p) := by
  intro i j hij
  have hpair : (p, i) = (p, j) :=
    RootIndexed.childAddress_joint_injective hij
  exact congrArg Prod.snd hpair

/-- Every realized slot beyond the finite cutoff has `N` strictly earlier
realized siblings in the full child set. -/
lemma lateChild_not_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (p : RootAddress m ℕ) (hp : p ∈ s)
    (horder : ω p.1 p.2 ∈ orderedSteps)
    (j : ℕ) (hNj : N ≤ j)
    (hj : survive (ω p.1 p.2) j) :
    ¬fullRankBelow N x ω (allMultiRootChildren s ω)
      (RootIndexed.childAddress p j) := by
  intro hbelow
  apply hbelow
  let t : Finset (RootAddress m ℕ) :=
    (Finset.range N).image (RootIndexed.childAddress p)
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : survive (ω p.1 p.2) i :=
      Step.IsSiblingClosed.survive_of_lt horder.1 hij hj
    constructor
    · exact ⟨p, hp, i, hreal, rfl⟩
    · exact candidateEarlier_ordered_siblings x ω p horder hij hj

/-- Every full-process child whose strict rank is below `N` belongs to the
finite first-`N`-slots candidate set. -/
lemma fullRankBelow_child_mem_candidates {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (horder : ∀ p ∈ s, ω p.1 p.2 ∈ orderedSteps)
    (q : RootAddress m ℕ)
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
lemma lateChild_earlier_forces_finite_rank {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (p : RootAddress m ℕ) (hp : p ∈ s)
    (horder : ω p.1 p.2 ∈ orderedSteps)
    (j : ℕ) (hNj : N ≤ j)
    (hj : survive (ω p.1 p.2) j)
    (q : RootAddress m ℕ)
    (hjq : candidateEarlier x ω (RootIndexed.childAddress p j) q) :
    N ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card := by
  classical
  let t : Finset (RootAddress m ℕ) :=
    (Finset.range N).image (RootIndexed.childAddress p)
  have htcard : t.card = N := by
    dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  have hsubset : t ⊆
      earlierCandidates x ω (multiRootCandidates N s ω) q := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : survive (ω p.1 p.2) i :=
      Step.IsSiblingClosed.survive_of_lt horder.1 hij hj
    have hcandidate : RootIndexed.childAddress p i ∈
        multiRootCandidates N s ω := by
      unfold multiRootCandidates
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hp, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, ?_⟩
      exact (mem_oneChildCandidate_iff ω p (RootIndexed.childAddress p i) i).2
        ⟨hreal, rfl⟩
    have hleft := candidateEarlier_ordered_siblings
      x ω p horder hij hj
    have hright : candidateEarlier x ω (RootIndexed.childAddress p i) q :=
      (candidateEarlier_iff_key_lt x ω _ _).2
        (lt_trans
          ((candidateEarlier_iff_key_lt x ω _ _).1 hleft)
          ((candidateEarlier_iff_key_lt x ω _ _).1 hjq))
    exact Finset.mem_filter.mpr ⟨hcandidate, hright⟩
  calc
    N = t.card := htcard.symm
    _ ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card :=
      Finset.card_le_card hsubset

/-- Finite-rank selection is not spoiled by omitted late-slot children. -/
lemma finiteLeftmost_mem_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (horder : ∀ p ∈ s, ω p.1 p.2 ∈ orderedSteps)
    (q : RootAddress m ℕ)
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
    · have hmem : RootIndexed.childAddress p j ∈ C := by
        unfold C multiRootCandidates
        apply Finset.mem_biUnion.mpr
        refine ⟨p, hp, ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨j, Finset.mem_range.mpr hjN,
          (mem_oneChildCandidate_iff ω p (RootIndexed.childAddress p j) j).2
            ⟨hj, rfl⟩⟩
      exact hrnot hmem
    · have hNj : N ≤ j := by omega
      have hlarge := lateChild_earlier_forces_finite_rank
        N x s ω p hp (horder p hp) j hNj hj q hrq
      change N ≤ (earlierCandidates x ω C q).card at hlarge
      omega

/-- A full-process top-`N` child has finite-candidate rank below `N`. -/
lemma fullRankBelow_mem_finiteLeftmost {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (horder : ∀ p ∈ s, ω p.1 p.2 ∈ orderedSteps)
    (q : RootAddress m ℕ)
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
lemma finiteLeftmost_eq_fullSelection {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (horder : ∀ p ∈ s, ω p.1 p.2 ∈ orderedSteps) :
    (↑(finiteLeftmost N x ω (multiRootCandidates N s ω)) :
      Set (RootAddress m ℕ)) =
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
