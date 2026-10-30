/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.Selection.NSelection.Mechanism.Finite.AtRank
public import Combinatorics.Matching.LowerTail

/-!
# Finite matching from lower-tail counts

Assume finite source and target populations, with linear orders on values.
## Public declarations

- `Combinatorics.Selection.NSelection.exists_injective_le_selectFirstNBy`:
  a retained population $R\subseteq S$ of size at most $N$ injects into the
  first-$N$ target candidates when the lower-tail counts of $S$ are bounded
  by those of the target population.
- `Combinatorics.Selection.NSelection.exists_injective_le_of_embedding_of_isFirstNBy`:
  if a finite retained population embeds injectively into a candidate set
  with $g(\operatorname{embed}(p))\leq f(p)$ and has size at most $N$, then
  it injectively matches into any selected set satisfying
  `IsFirstNBy N g candidates selected`, preserving the same value bound.
- `Combinatorics.Selection.NSelection.exists_injective_le_of_dependent_embedding_of_isFirstNBy`
  gives the same conclusion when the embedding is supplied only together
  with a proof that each source label belongs to the retained population.

The generic finite lower-tail matching theorem is
`Combinatorics.Matching.exists_injective_le_of_filter_card_le`; the results
here specialize it to capacity-constrained selections. They do not depend on
the concrete equal-rank matching map in `NSelection/Matching/ByRank.lean`.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

variable {Source Target Value : Type*}

/-- A retained population of size at most `N` has an injective matching into
the dynamically selected leftmost `N` target candidates whenever the original
candidate populations satisfy the lower-tail comparison. -/
theorem exists_injective_le_selectFirstNBy
    [DecidableEq Source] [LinearOrder Target] [LinearOrder Value]
    (N : ℕ) (sourceValue : Source → Value) (targetValue : Target → Value)
    (retained source : Finset Source) (target : Finset Target)
    (hretained : retained ⊆ source)
    (hcard : retained.card ≤ N)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card) :
    ∃ matchParticle : (p : Source) → p ∈ retained → Target,
      (∀ p hp, matchParticle p hp ∈ selectFirstNBy N targetValue target) ∧
      (∀ p hp, targetValue (matchParticle p hp) ≤ sourceValue p) ∧
      (∀ p hp q hq, matchParticle p hp = matchParticle q hq → p = q) := by
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_filter_card_le
      sourceValue targetValue retained (selectFirstNBy N targetValue target)
      (filter_card_le_filter_selectFirstNBy N sourceValue targetValue retained source
        target hretained hcard hthreshold)
  refine ⟨fun p hp => (f ⟨p, hp⟩).1, ?_, ?_, ?_⟩
  · intro p hp
    exact (f ⟨p, hp⟩).2
  · intro p hp
    exact hle ⟨p, hp⟩
  · intro p hp q hq heq
    have hsub : (⟨p, hp⟩ : {p : Source // p ∈ retained}) = ⟨q, hq⟩ := by
      apply hinj
      exact Subtype.ext heq
    exact congrArg Subtype.val hsub

/-- Match a finite retained population into an abstract first-`N` segment of
an arbitrary target candidate set.  The candidate set itself may be
uncountable; only the retained and selected populations are finite. -/
theorem exists_injective_le_of_embedding_of_isFirstNBy
    [DecidableEq Source] [LinearOrder Target] [LinearOrder Value]
    (N : ℕ) (sourceValue : Source → Value) (targetValue : Target → Value)
    (retained : Finset Source) (targetCandidates : Set Target)
    (selected : Finset Target)
    (hselected : IsFirstNBy N targetValue targetCandidates selected)
    (hcard : retained.card ≤ N)
    (embed : Source → Target)
    (hembed_mem : ∀ p ∈ retained, embed p ∈ targetCandidates)
    (hembed_inj : Set.InjOn embed ↑retained)
    (hembed_le : ∀ p ∈ retained,
      targetValue (embed p) ≤ sourceValue p) :
    ∃ matchParticle : (p : Source) → p ∈ retained → Target,
      (∀ p hp, matchParticle p hp ∈ selected) ∧
      (∀ p hp, targetValue (matchParticle p hp) ≤ sourceValue p) ∧
      (∀ p hp q hq, matchParticle p hp = matchParticle q hq → p = q) := by
  classical
  let mapped : Finset Target := retained.image embed
  have hmappedSubset : ↑mapped ⊆ targetCandidates := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hembed_mem p hp
  have hmappedCard : mapped.card = retained.card := by
    exact Finset.card_image_iff.mpr fun p hp q hq hpq =>
      hembed_inj hp hq hpq
  have hthreshold : ∀ a : Value,
      (retained.filter fun p => sourceValue p ≤ a).card ≤
        (selected.filter fun q => targetValue q ≤ a).card := by
    intro a
    have hsourceMapped :
        (retained.filter fun p => sourceValue p ≤ a).card ≤
          (mapped.filter fun q => targetValue q ≤ a).card := by
      apply Finset.card_le_card_of_injOn embed
      · intro p hp
        obtain ⟨hpRetained, hpValue⟩ := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨p, hpRetained, rfl⟩,
          (hembed_le p hpRetained).trans hpValue⟩
      · intro p hp q hq hpq
        exact hembed_inj (Finset.mem_filter.mp hp).1
          (Finset.mem_filter.mp hq).1 hpq
    exact hsourceMapped.trans
      (filter_card_le_filter_of_isFirstNBy N targetValue targetCandidates
        selected mapped hselected hmappedSubset
        (by rw [hmappedCard]; exact hcard) a)
  obtain ⟨f, hinj, hle⟩ :=
    Combinatorics.Matching.exists_injective_le_of_filter_card_le
      sourceValue targetValue retained selected hthreshold
  refine ⟨fun p hp => (f ⟨p, hp⟩).1, ?_, ?_, ?_⟩
  · intro p hp
    exact (f ⟨p, hp⟩).2
  · intro p hp
    exact hle ⟨p, hp⟩
  · intro p hp q hq heq
    have hsub : (⟨p, hp⟩ : {p : Source // p ∈ retained}) = ⟨q, hq⟩ := by
      apply hinj
      exact Subtype.ext heq
    exact congrArg Subtype.val hsub

/-- Dependent-witness form of the preceding theorem.  It is convenient when
the embedding is defined only after proving that a particle belongs to the
retained population. -/
theorem exists_injective_le_of_dependent_embedding_of_isFirstNBy
    [DecidableEq Source] [LinearOrder Target] [LinearOrder Value]
    (N : ℕ) (sourceValue : Source → Value) (targetValue : Target → Value)
    (retained : Finset Source) (targetCandidates : Set Target)
    (selected : Finset Target)
    (hselected : IsFirstNBy N targetValue targetCandidates selected)
    (hcard : retained.card ≤ N)
    (embed : (p : Source) → p ∈ retained → Target)
    (hembed_mem : ∀ p hp, embed p hp ∈ targetCandidates)
    (hembed_inj : ∀ p hp q hq, embed p hp = embed q hq → p = q)
    (hembed_le : ∀ p hp,
      targetValue (embed p hp) ≤ sourceValue p) :
    ∃ matchParticle : (p : Source) → p ∈ retained → Target,
      (∀ p hp, matchParticle p hp ∈ selected) ∧
      (∀ p hp, targetValue (matchParticle p hp) ≤ sourceValue p) ∧
      (∀ p hp q hq, matchParticle p hp = matchParticle q hq → p = q) := by
  classical
  let attached : Finset {p : Source // p ∈ retained} := Finset.univ
  have hattachedCard : attached.card = retained.card := by
    simp [attached]
  obtain ⟨matchAttached, hmem, hle, hinj⟩ :=
    exists_injective_le_of_embedding_of_isFirstNBy N
      (fun p : {p : Source // p ∈ retained} => sourceValue p.1)
      targetValue attached targetCandidates selected hselected
      (by rw [hattachedCard]; exact hcard)
      (fun p => embed p.1 p.2)
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
