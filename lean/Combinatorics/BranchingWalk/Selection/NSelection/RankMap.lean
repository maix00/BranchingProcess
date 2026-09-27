import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
import Combinatorics.BranchingWalk.Selection.NSelection.AtRank
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
  apply exists_injective_le_of_filter_card_le sourceValue targetValue
    retained selected
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


/-- Lower-tail count domination implies the spatial inequality for particles
of equal dynamic rank.  This is the deterministic core of the canonical
rank matching. -/
theorem value_le_of_rankBy_eq_of_filter_card_le
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card)
    {p : Source} (hp : p ∈ source) {q : Target}
    (hrank : rankBy targetValue target q =
      rankBy sourceValue source p) :
    targetValue q ≤ sourceValue p := by
  by_contra hle
  have hlt : sourceValue p < targetValue q := lt_of_not_ge hle
  let sourceBelow := source.filter fun r =>
    valueKey sourceValue r < valueKey sourceValue p
  let targetBelow := target.filter fun r =>
    valueKey targetValue r < valueKey targetValue q
  have hpNotBelow : p ∉ sourceBelow := by
    simp [sourceBelow]
  have hsourceSubset : insert p sourceBelow ⊆
      source.filter fun r => sourceValue r ≤ sourceValue p := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_filter.mpr ⟨hp, le_rfl⟩
    · obtain ⟨hrs, hrkey⟩ := Finset.mem_filter.mp hr
      have hrvalue : sourceValue r ≤ sourceValue p := by
        rcases Prod.Lex.lt_iff.mp hrkey with h | h
        · exact le_of_lt h
        · exact le_of_eq h.1
      exact Finset.mem_filter.mpr ⟨hrs, hrvalue⟩
  have htargetSubset :
      target.filter (fun r => targetValue r ≤ sourceValue p) ⊆ targetBelow := by
    intro r hr
    obtain ⟨hrt, hrvalue⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr
      ⟨hrt, valueKey_lt_of_value_lt targetValue (hrvalue.trans_lt hlt)⟩
  have hsourceCard : rankBy sourceValue source p + 1 ≤
      (source.filter fun r => sourceValue r ≤ sourceValue p).card := by
    rw [rankBy_eq_card_filter]
    change sourceBelow.card + 1 ≤ _
    rw [← Finset.card_insert_of_notMem hpNotBelow]
    exact Finset.card_le_card hsourceSubset
  have htargetCard :
      (target.filter fun r => targetValue r ≤ sourceValue p).card ≤
        rankBy targetValue target q := by
    rw [rankBy_eq_card_filter]
    exact Finset.card_le_card htargetSubset
  have hcount := hthreshold (sourceValue p)
  omega

/-- Match a source particle to the target particle having the same dynamic
rank.  The result is optional because the target may be too small. -/
noncomputable def particleAtSourceRankBy
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target) (p : Source) :
    Option Target :=
  particleAtRankBy targetValue target (rankBy sourceValue source p)

@[simp] theorem particleAtSourceRankBy_eq_some_iff
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    {sourceValue : Source → Value} {targetValue : Target → Value}
    {source : Finset Source} {target : Finset Target}
    {p : Source} {q : Target} :
    particleAtSourceRankBy sourceValue targetValue source target p = some q ↔
      q ∈ target ∧ rankBy targetValue target q =
        rankBy sourceValue source p := by
  exact particleAtRankBy_eq_some_iff

/-- The inverse equal-rank match is defined only on the target population.
The membership guard is essential: the rank of a label outside `target` may
coincide with an occupied rank and must not duplicate a source coordinate. -/
noncomputable def preimageByRank
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target) (q : Target) :
    Option Source :=
  if q ∈ target then
    particleAtSourceRankBy targetValue sourceValue target source q
  else none

@[simp] theorem preimageByRank_eq_some_iff
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    {sourceValue : Source → Value} {targetValue : Target → Value}
    {source : Finset Source} {target : Finset Target}
    {q : Target} {p : Source} :
    preimageByRank sourceValue targetValue source target q = some p ↔
      q ∈ target ∧ p ∈ source ∧
        rankBy sourceValue source p = rankBy targetValue target q := by
  by_cases hq : q ∈ target
  · simp only [preimageByRank, hq, ↓reduceIte,
      particleAtSourceRankBy_eq_some_iff]
    tauto
  · simp [preimageByRank, hq]

/-- The inverse equal-rank match uses a source label at most once. -/
theorem preimageByRank_leftUnique
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    {q₁ q₂ : Target} {p : Source}
    (h₁ : preimageByRank sourceValue targetValue source target q₁ = some p)
    (h₂ : preimageByRank sourceValue targetValue source target q₂ = some p) :
    q₁ = q₂ := by
  obtain ⟨hq₁, _, hr₁⟩ := preimageByRank_eq_some_iff.mp h₁
  obtain ⟨hq₂, _, hr₂⟩ := preimageByRank_eq_some_iff.mp h₂
  apply rankBy_injOn targetValue target hq₁ hq₂
  exact hr₁.symm.trans hr₂

/-- For fixed finite source and target populations there are only finitely
many guarded inverse maps, independently of the ranking values. -/
theorem preimageByRank_maps_finite
    {Source Target : Type*} (source : Finset Source) (target : Finset Target) :
    {f : Target → Option Source |
      (∀ q, q ∉ target → f q = none) ∧
      (∀ q p, f q = some p → p ∈ source)}.Finite := by
  classical
  let S : Set (Target → Option Source) :=
    {f | (∀ q, q ∉ target → f q = none) ∧
      (∀ q p, f q = some p → p ∈ source)}
  let code : S → ({q : Target // q ∈ target} →
      Option {p : Source // p ∈ source}) := fun f q =>
    match h : f.1 q.1 with
    | none => none
    | some p => some ⟨p, f.2.2 q.1 p h⟩
  have hdecode (f : S) (q : {q : Target // q ∈ target}) :
      Option.map Subtype.val (code f q) = f.1 q.1 := by
    simp only [code]
    split <;> rename_i h
    · exact h.symm
    · simp only [Option.map_some]
      exact h.symm
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ target
    · rw [← hdecode f ⟨q, hq⟩, ← hdecode g ⟨q, hq⟩,
        congrFun hfg ⟨q, hq⟩]
    · rw [f.2.1 q hq, g.2.1 q hq]
  let _ : Finite S := Finite.of_injective code hcode
  exact Set.finite_coe_iff.mp inferInstance

/-- A source member has a same-rank target whenever the target has at least
as many particles. -/
theorem particleAtSourceRankBy_ne_none
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    {source : Finset Source} {target : Finset Target}
    {p : Source} (hp : p ∈ source) (hcard : source.card ≤ target.card) :
    particleAtSourceRankBy sourceValue targetValue source target p ≠ none := by
  intro hnone
  have hle : target.card ≤ rankBy sourceValue source p :=
    particleAtRankBy_eq_none_iff.mp hnone
  exact (not_le_of_gt ((rankBy_lt_card_of_mem sourceValue hp).trans_le hcard)) hle

/-- The target particle having the same dynamic rank as a source member.

The membership proof is an argument because existence only follows on the
source set.  This avoids adding an arbitrary default particle to either
ambient type. -/
noncomputable def matchByRank
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (p : Source) (hp : p ∈ source) : Target :=
  Option.get
    (particleAtSourceRankBy sourceValue targetValue source target p)
    (Option.isSome_iff_ne_none.mpr
      (particleAtSourceRankBy_ne_none sourceValue targetValue hp hcard))

theorem particleAtSourceRankBy_matchByRank
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (p : Source) (hp : p ∈ source) :
    particleAtSourceRankBy sourceValue targetValue source target p =
      some (matchByRank sourceValue targetValue source target hcard p hp) := by
  unfold matchByRank
  exact (Option.some_get _).symm

theorem matchByRank_mem
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (p : Source) (hp : p ∈ source) :
    matchByRank sourceValue targetValue source target hcard p hp ∈ target := by
  exact (particleAtSourceRankBy_eq_some_iff.mp
    (particleAtSourceRankBy_matchByRank sourceValue targetValue source target
      hcard p hp)).1

theorem rankBy_matchByRank
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (p : Source) (hp : p ∈ source) :
    rankBy targetValue target
        (matchByRank sourceValue targetValue source target hcard p hp) =
      rankBy sourceValue source p := by
  exact (particleAtSourceRankBy_eq_some_iff.mp
    (particleAtSourceRankBy_matchByRank sourceValue targetValue source target
      hcard p hp)).2

/-- Looking up a source particle at the dynamic rank of its matched target
recovers that source particle.  This is the inverse interface used when
source steps are installed at matched target labels. -/
theorem particleAtSourceRankBy_matchByRank_target
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (p : Source) (hp : p ∈ source) :
    particleAtSourceRankBy targetValue sourceValue target source
        (matchByRank sourceValue targetValue source target hcard p hp) =
      some p := by
  apply particleAtSourceRankBy_eq_some_iff.mpr
  exact ⟨hp,
    (rankBy_matchByRank sourceValue targetValue source target hcard p hp).symm⟩

/-- Equal-rank matching is injective on the source subtype. -/
theorem matchByRank_injective
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card) :
    Function.Injective fun p : {p // p ∈ source} =>
      matchByRank sourceValue targetValue source target hcard p.1 p.2 := by
  intro p q heq
  apply Subtype.ext
  apply rankBy_injOn sourceValue source p.2 q.2
  change matchByRank sourceValue targetValue source target hcard p.1 p.2 =
    matchByRank sourceValue targetValue source target hcard q.1 q.2 at heq
  rw [← rankBy_matchByRank sourceValue targetValue source target hcard p.1 p.2,
    ← rankBy_matchByRank sourceValue targetValue source target hcard q.1 q.2]
  exact congrArg (rankBy targetValue target) heq

/-- Lower-tail count domination makes equal-rank matching spatially
dominating. -/
theorem matchByRank_value_le
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hcard : source.card ≤ target.card)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card)
    (p : Source) (hp : p ∈ source) :
    targetValue (matchByRank sourceValue targetValue source target hcard p hp) ≤
      sourceValue p := by
  apply value_le_of_rankBy_eq_of_filter_card_le sourceValue targetValue
    source target hthreshold hp
  exact rankBy_matchByRank sourceValue targetValue source target hcard p hp

/-- Extend equal-rank matching to the ambient particle type by fixing labels
outside the source population.  The fallback is never used by the coupling
invariant, but makes the match directly usable as a cloud map. -/
noncomputable def matchByRankOrSelf
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    (p : Particle) : Particle :=
  if hp : p ∈ source then
    matchByRank sourceValue targetValue source target hcard p hp
  else p

@[simp] theorem matchByRankOrSelf_of_mem
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    {p : Particle} (hp : p ∈ source) :
    matchByRankOrSelf sourceValue targetValue source target hcard p =
      matchByRank sourceValue targetValue source target hcard p hp := by
  simp [matchByRankOrSelf, hp]

@[simp] theorem matchByRankOrSelf_of_not_mem
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    {p : Particle} (hp : p ∉ source) :
    matchByRankOrSelf sourceValue targetValue source target hcard p = p := by
  simp [matchByRankOrSelf, hp]

theorem matchByRankOrSelf_mem
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    {p : Particle} (hp : p ∈ source) :
    matchByRankOrSelf sourceValue targetValue source target hcard p ∈ target := by
  rw [matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hp]
  exact matchByRank_mem sourceValue targetValue source target hcard p hp

/-- On the source population, the optional inverse also recovers the total
ambient equal-rank match. -/
theorem particleAtSourceRankBy_matchByRankOrSelf
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    {p : Particle} (hp : p ∈ source) :
    particleAtSourceRankBy targetValue sourceValue target source
        (matchByRankOrSelf sourceValue targetValue source target hcard p) =
      some p := by
  rw [matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hp]
  exact particleAtSourceRankBy_matchByRank_target sourceValue targetValue
    source target hcard p hp

theorem matchByRankOrSelf_injOn
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card) :
    Set.InjOn (matchByRankOrSelf sourceValue targetValue source target hcard)
      ↑source := by
  intro p hp q hq heq
  have hp' : p ∈ source := hp
  have hq' : q ∈ source := hq
  have hsub : (⟨p, hp⟩ : {p // p ∈ source}) = ⟨q, hq⟩ := by
    apply matchByRank_injective sourceValue targetValue source target hcard
    rw [matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hp',
      matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hq'] at heq
    exact heq
  exact congrArg Subtype.val hsub

theorem matchByRankOrSelf_value_le
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Particle → Value)
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card)
    {p : Particle} (hp : p ∈ source) :
    targetValue
        (matchByRankOrSelf sourceValue targetValue source target hcard p) ≤
      sourceValue p := by
  rw [matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hp]
  exact matchByRank_value_le sourceValue targetValue source target hcard
    hthreshold p hp

end Combinatorics.Branching.Selection.NSelection
