/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.ByValue
public import Mathlib.Data.Set.Card

/-!
# Selecting the first N points of a possibly infinite population

`selectFirstNBy` is the finite algorithm.  This file supplies the abstract
interface needed before that algorithm can be applied to an infinite
candidate set.  Lower local finiteness rules out descending accumulation at
the selected edge: every candidate has only finitely many predecessors.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

variable {ι Value : Type*}

/-- Every principal lower section of the candidate population is finite.
This is the order-theoretic condition needed for selecting finitely many
leftmost particles; it is stronger and more directional than local finiteness
on bounded compact sets. -/
def IsLowerFiniteBy [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (candidates : Set ι) : Prop :=
  ∀ p ∈ candidates,
    {q | q ∈ candidates ∧ valueKey value q ≤ valueKey value p}.Finite

/-- Specification of the first `N` particles of an arbitrary candidate set.
For a finite population its cardinality is `min N card`; for an infinite
population it is exactly `N`.  The lower-set clause characterizes the spatial
initial segment independently of its construction. -/
structure IsFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι)
    (selected : Finset ι) : Prop where
  subset : ↑selected ⊆ candidates
  card_finite : ∀ h : Set.Finite candidates,
    selected.card = min N h.toFinset.card
  card_infinite : Set.Infinite candidates → selected.card = N
  lower : ∀ p ∈ selected, ∀ q ∈ candidates,
    valueKey value q < valueKey value p → q ∈ selected

/-- A candidate population admits its first `N` particles when some finite
set satisfies the intrinsic initial-segment specification. -/
def AdmitsFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι) : Prop :=
  ∃ selected, IsFirstNBy N value candidates selected

/-- Finite candidate populations admit the first `N` particles through the
finite dynamic selection algorithm. -/
theorem admitsFirstNBy_of_finite [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) {candidates : Set ι}
    (hfinite : Set.Finite candidates) :
    AdmitsFirstNBy N value candidates := by
  classical
  refine ⟨selectFirstNBy N value hfinite.toFinset, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hfinite.mem_toFinset.mp
      (selectFirstNBy_subset N value hfinite.toFinset hp)
  · intro h
    rw [card_selectFirstNBy]
  · exact fun hinfinite => (hinfinite hfinite).elim
  · intro p hp q hq hqp
    apply mem_selectFirstNBy_of_key_lt hp
    · exact hfinite.mem_toFinset.mpr hq
    · exact hqp

/-- Lower local finiteness makes the first `N` particles exist even when the
candidate population is infinite. -/
theorem admitsFirstNBy_of_infinite_of_lowerFinite
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) {candidates : Set ι}
    (hinfinite : Set.Infinite candidates)
    (hlower : IsLowerFiniteBy value candidates) :
    AdmitsFirstNBy N value candidates := by
  classical
  by_cases hN : N = 0
  · subst N
    refine ⟨∅, ⟨by simp, ?_, ?_, by simp⟩⟩
    · intro h
      simp
    · intro _
      simp
  · obtain ⟨seed, hseed, hseedCard⟩ :=
      Set.Infinite.exists_subset_card_eq hinfinite N
    have hseedNonempty : seed.Nonempty :=
      Finset.card_pos.mp (by simpa [hseedCard] using Nat.zero_lt_of_ne_zero hN)
    obtain ⟨bound, hboundSeed, hbound⟩ :=
      Finset.exists_max_image seed (valueKey value) hseedNonempty
    let lowerSet : Set ι :=
      {q | q ∈ candidates ∧ valueKey value q ≤ valueKey value bound}
    have hboundCandidate : bound ∈ candidates := hseed hboundSeed
    have hlowerFinite : lowerSet.Finite := hlower bound hboundCandidate
    have hseedLower : ↑seed ⊆ lowerSet := by
      intro q hq
      exact ⟨hseed hq, hbound q hq⟩
    let selected := selectFirstNBy N value hlowerFinite.toFinset
    have hlowerCard : N ≤ hlowerFinite.toFinset.card := by
      rw [← hseedCard]
      exact Finset.card_le_card (fun q hq =>
        hlowerFinite.mem_toFinset.mpr (hseedLower hq))
    have hselectedCard : selected.card = N := by
      simp [selected, card_selectFirstNBy, min_eq_left hlowerCard]
    refine ⟨selected, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro p hp
      exact (hlowerFinite.mem_toFinset.mp
        (selectFirstNBy_subset N value hlowerFinite.toFinset hp)).1
    · intro hfinite
      exact (hinfinite hfinite).elim
    · intro _
      exact hselectedCard
    · intro p hp q hq hqp
      apply mem_selectFirstNBy_of_key_lt hp
      apply hlowerFinite.mem_toFinset.mpr
      have hpLower := hlowerFinite.mem_toFinset.mp
        (selectFirstNBy_subset N value hlowerFinite.toFinset hp)
      exact ⟨hq, le_trans (le_of_lt hqp) hpLower.2⟩
      exact hqp

/-- Lower local finiteness is a sufficient condition for existence of the
first `N` particles, covering finite and infinite candidate populations. -/
theorem admitsFirstNBy_of_lowerFinite
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) {candidates : Set ι}
    (hlower : IsLowerFiniteBy value candidates) :
    AdmitsFirstNBy N value candidates := by
  classical
  exact candidates.finite_or_infinite.elim
    (admitsFirstNBy_of_finite N value)
    (fun hinfinite => admitsFirstNBy_of_infinite_of_lowerFinite
      N value hinfinite hlower)

/-- The abstract selected set, available only after existence has been
proved. -/
noncomputable def selectFirstNFromSet [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι)
    (h : AdmitsFirstNBy N value candidates) : Finset ι :=
  h.choose

theorem selectFirstNFromSet_spec [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι)
    (h : AdmitsFirstNBy N value candidates) :
    IsFirstNBy N value candidates
      (selectFirstNFromSet N value candidates h) :=
  h.choose_spec

theorem IsFirstNBy.card_le [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {candidates : Set ι}
    {selected : Finset ι}
    (h : IsFirstNBy N value candidates selected) :
    selected.card ≤ N := by
  rcases candidates.finite_or_infinite with hfinite | hinfinite
  · rw [h.card_finite hfinite]
    exact min_le_left _ _
  · rw [h.card_infinite hinfinite]

/-- The first-`N` property depends only on observation values at candidate
points. This permits measurable total extensions of a generation-level
observation without changing its intrinsic selection. -/
theorem IsFirstNBy.congr_value [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value other : ι → Value} {candidates : Set ι}
    {selected : Finset ι}
    (h : IsFirstNBy N value candidates selected)
    (heq : Set.EqOn value other candidates) :
    IsFirstNBy N other candidates selected := by
  refine ⟨h.subset, h.card_finite, h.card_infinite, ?_⟩
  intro p hp q hq hqp
  apply h.lower p hp q hq
  simpa [valueKey, heq (h.subset hp), heq hq] using hqp

/-- The first-`N` initial segment is unique because `valueKey` is a linear
order, including its deterministic label tie breaker. -/
theorem IsFirstNBy.unique [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {candidates : Set ι}
    {selected other : Finset ι}
    (hselected : IsFirstNBy N value candidates selected)
    (hother : IsFirstNBy N value candidates other) :
    selected = other := by
  have hcard : selected.card = other.card := by
    rcases candidates.finite_or_infinite with hfinite | hinfinite
    · rw [hselected.card_finite hfinite, hother.card_finite hfinite]
    · rw [hselected.card_infinite hinfinite, hother.card_infinite hinfinite]
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    by_contra hpother
    have hnsubset : ¬other ⊆ selected := by
      intro hsubset
      have heq : other = selected :=
        Finset.eq_of_subset_of_card_le hsubset hcard.le
      exact hpother (heq ▸ hp)
    obtain ⟨q, hqother, hqselected⟩ := Finset.not_subset.mp hnsubset
    rcases lt_trichotomy (valueKey value q) (valueKey value p) with hqp | hqp | hqp
    · exact hqselected
        (hselected.lower p hp q (hother.subset hqother) hqp)
    · have : q = p := congrArg Prod.snd hqp
      exact hpother (this ▸ hqother)
    · exact hpother
        (hother.lower q hqother p (hselected.subset hp) hqp)
  · exact hcard.ge

/-- Membership in the first-`N` segment is characterized by having fewer
than `N` strict predecessors in the candidate population. -/
theorem IsFirstNBy.mem_iff_ncard_lt
    [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {candidates : Set ι}
    {selected : Finset ι}
    (h : IsFirstNBy N value candidates selected) (p : ι) :
    p ∈ selected ↔ p ∈ candidates ∧
      {q | q ∈ candidates ∧ valueKey value q < valueKey value p}.Finite ∧
      {q | q ∈ candidates ∧ valueKey value q < valueKey value p}.ncard < N := by
  let lower : Set ι :=
    {q | q ∈ candidates ∧ valueKey value q < valueKey value p}
  constructor
  · intro hp
    have hlower : lower ⊆ ↑(selected.erase p) := by
      intro q hq
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun hqp => by simpa [hqp] using hq.2, h.lower p hp q hq.1 hq.2⟩)
    refine ⟨h.subset hp, ?_, ?_⟩
    · exact (selected.erase p).finite_toSet.subset hlower
    have hle : lower.ncard ≤ (selected.erase p).card := calc
      lower.ncard ≤ (↑(selected.erase p) : Set ι).ncard :=
        Set.ncard_le_ncard hlower (selected.erase p).finite_toSet
      _ = (selected.erase p).card := Set.ncard_coe_finset _
    exact lt_of_le_of_lt hle
      ((Finset.card_erase_lt_of_mem hp).trans_le h.card_le)
  · rintro ⟨hpcandidate, hlowerFinite, hlowerCard⟩
    change lower.Finite at hlowerFinite
    change lower.ncard < N at hlowerCard
    by_contra hpselected
    have hcard : selected.card = N := by
      rcases candidates.finite_or_infinite with hfinite | hinfinite
      · by_cases hcand : N ≤ hfinite.toFinset.card
        · rw [h.card_finite hfinite, min_eq_left hcand]
        · have hcandLe : hfinite.toFinset.card ≤ N :=
            (Nat.lt_of_not_ge hcand).le
          have heq : selected = hfinite.toFinset :=
            Finset.eq_of_subset_of_card_le
              (fun q hq => hfinite.mem_toFinset.mpr (h.subset hq))
              (by rw [h.card_finite hfinite, min_eq_right hcandLe])
          exact (hpselected
            (heq ▸ hfinite.mem_toFinset.mpr hpcandidate)).elim
      · exact h.card_infinite hinfinite
    have hsubset : (↑selected : Set ι) ⊆ lower := by
      intro q hq
      refine ⟨h.subset hq, ?_⟩
      rcases lt_trichotomy (valueKey value q) (valueKey value p) with hqp | hqp | hqp
      · exact hqp
      · have : q = p := congrArg Prod.snd hqp
        exact (hpselected (this ▸ hq)).elim
      · exact (hpselected (h.lower q hq p hpcandidate hqp)).elim
    have hle : selected.card ≤ lower.ncard := by
      simpa using Set.ncard_le_ncard hsubset
        hlowerFinite
    omega

/-- Increasing the capacity can only enlarge the intrinsic initial segment.
This statement applies directly to infinite candidate populations. -/
theorem IsFirstNBy.subset_of_le
    [LinearOrder ι] [LinearOrder Value]
    {N M : ℕ} {value : ι → Value} {candidates : Set ι}
    {selected larger : Finset ι}
    (hselected : IsFirstNBy N value candidates selected)
    (hlarger : IsFirstNBy M value candidates larger)
    (hNM : N ≤ M) : selected ⊆ larger := by
  intro p hp
  obtain ⟨hpcandidate, hfinite, hcard⟩ :=
    (hselected.mem_iff_ncard_lt p).mp hp
  apply (hlarger.mem_iff_ncard_lt p).mpr
  exact ⟨hpcandidate, hfinite, hcard.trans_le hNM⟩

theorem mem_selectFirstNFromSet_iff
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι)
    (h : AdmitsFirstNBy N value candidates) (p : ι) :
    p ∈ selectFirstNFromSet N value candidates h ↔
      p ∈ candidates ∧
        {q | q ∈ candidates ∧ valueKey value q < valueKey value p}.Finite ∧
        {q | q ∈ candidates ∧ valueKey value q < valueKey value p}.ncard < N :=
  (selectFirstNFromSet_spec N value candidates h).mem_iff_ncard_lt p

/-- An abstract first-`N` segment dominates every finite subpopulation of the
same candidates whose cardinality is at most `N`, at every value threshold.
The ambient candidate set may be uncountable. -/
theorem filter_card_le_filter_of_isFirstNBy
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (candidates : Set ι)
    (selected retained : Finset ι)
    (hselected : IsFirstNBy N value candidates selected)
    (hretained : ↑retained ⊆ candidates)
    (hcard : retained.card ≤ N) (a : Value) :
    (retained.filter fun q => value q ≤ a).card ≤
      (selected.filter fun q => value q ≤ a).card := by
  classical
  by_cases hp : ∃ p ∈ selected, a < value p
  · obtain ⟨p, hpselected, hap⟩ := hp
    apply Finset.card_le_card
    intro q hq
    obtain ⟨hqretained, hqa⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨hselected.lower p hpselected q (hretained hqretained) ?_, hqa⟩
    change Prod.Lex (· < ·) (· < ·) (value q, q) (value p, p)
    exact Prod.Lex.left q p (lt_of_le_of_lt hqa hap)
  · have hselectedBelow :
        selected.filter (fun q => value q ≤ a) = selected := by
      apply Finset.filter_eq_self.mpr
      intro p hpselected
      exact le_of_not_gt (fun hap => hp ⟨p, hpselected, hap⟩)
    rw [hselectedBelow]
    have hfilteredCard :
        (retained.filter fun q => value q ≤ a).card ≤ N :=
      (Finset.card_filter_le _ _).trans hcard
    rcases candidates.finite_or_infinite with hfinite | hinfinite
    · rw [hselected.card_finite hfinite]
      apply le_min hfilteredCard
      exact (Finset.card_filter_le _ _).trans
        (Finset.card_le_card fun q hq =>
          hfinite.mem_toFinset.mpr (hretained hq))
    · rw [hselected.card_infinite hinfinite]
      exact hfilteredCard

end Combinatorics.Branching.Selection.NSelection

end
