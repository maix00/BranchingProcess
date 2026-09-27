import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
import Mathlib.Combinatorics.Hall.Basic

/-!
# Matching from lower-tail counts

For two finite populations on a line, domination of every lower-tail count
produces one coherent injective matching, with every target weakly to the left
of its source.  The proof uses the finite Hall marriage theorem already in
mathlib.  Particle identity and observed value are separate types.
-/

namespace Combinatorics.Branching.Selection.NSelection

variable {Source Target Value : Type*}

/-- Lower-tail count domination is equivalent to enough eligible targets for
an injective matching.  This direction constructs the matching. -/
theorem exists_injective_le_of_filter_card_le
    [DecidableEq Source] [DecidableEq Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card) :
    ∃ matchParticle : (p : Source) → p ∈ source → Target,
      (∀ p hp, matchParticle p hp ∈ target) ∧
      (∀ p hp, targetValue (matchParticle p hp) ≤ sourceValue p) ∧
      (∀ p hp q hq, matchParticle p hp = matchParticle q hq → p = q) := by
  classical
  let r : {p : Source // p ∈ source} → {q : Target // q ∈ target} → Prop :=
    fun p q => targetValue q.1 ≤ sourceValue p.1
  have hHall : ∀ A : Finset {p : Source // p ∈ source},
      A.card ≤ (Finset.univ.filter fun q : {q : Target // q ∈ target} =>
        ∃ p ∈ A, r p q).card := by
    intro A
    by_cases hA : A.Nonempty
    · obtain ⟨pmax, hpmax, hmax⟩ :=
        Finset.exists_max_image A
          (fun p : {p : Source // p ∈ source} => sourceValue p.1) hA
      have hAtoSource : A.card ≤
          (source.filter fun p => sourceValue p ≤ sourceValue pmax.1).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : {p : Source // p ∈ source} => p.1)
        · intro p hp
          exact Finset.mem_filter.mpr
            ⟨p.2, hmax p hp⟩
        · intro p _ q _ hpq
          exact Subtype.ext hpq
      have htoTarget := (hthreshold (sourceValue pmax.1))
      have htargetToRel :
          (target.filter fun q => targetValue q ≤ sourceValue pmax.1).card ≤
            (Finset.univ.filter fun q : {q : Target // q ∈ target} =>
              ∃ p ∈ A, r p q).card := by
        have hattach :
            (target.attach.filter fun q => targetValue q.1 ≤ sourceValue pmax.1).card =
              (target.filter fun q => targetValue q ≤ sourceValue pmax.1).card := by
          have h := congrArg Finset.card
            (Finset.filter_attach
              (fun q : Target => targetValue q ≤ sourceValue pmax.1) target)
          simpa using h
        have huniv : target.attach = (Finset.univ : Finset {q : Target // q ∈ target}) := by
          ext q
          simp
        rw [← hattach, huniv]
        apply Finset.card_le_card
        intro q hq
        obtain ⟨_, hqle⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨pmax, hpmax, hqle⟩⟩
      exact hAtoSource.trans (htoTarget.trans htargetToRel)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp
  have hex :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hHall
  obtain ⟨f, hinj, hrel⟩ := hex
  refine ⟨fun p hp => (f ⟨p, hp⟩).1, ?_, ?_, ?_⟩
  · intro p hp
    exact (f ⟨p, hp⟩).2
  · intro p hp
    exact hrel ⟨p, hp⟩
  · intro p hp q hq heq
    have hsub : (⟨p, hp⟩ : {p : Source // p ∈ source}) = ⟨q, hq⟩ := by
      apply hinj
      exact Subtype.ext heq
    exact congrArg Subtype.val hsub

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
  apply exists_injective_le_of_filter_card_le sourceValue targetValue retained
    (selectFirstNBy N targetValue target)
  exact filter_card_le_filter_selectFirstNBy N sourceValue targetValue retained source
    target hretained hcard hthreshold

end Combinatorics.Branching.Selection.NSelection
