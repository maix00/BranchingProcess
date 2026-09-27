import Combinatorics.BranchingWalk.Selection.NSelection.ByValue
import Mathlib.Data.Set.Card

/-!
# Selecting the first N points of a possibly infinite population

`selectFirstNBy` is the finite algorithm.  This file supplies the abstract
interface needed before that algorithm can be applied to an infinite
candidate set.  Lower local finiteness rules out descending accumulation at
the selected edge: every candidate has only finitely many predecessors.
-/

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
