/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
public import Combinatorics.BranchingWalk.Selection.NSelection.AtRank
/-!
# Equal-rank matching

This layer defines the optional inverse, total equal-rank matching, and their
finite-population identities.  The Hall existence theorems live separately in
NSelection/Hall.lean.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

variable {Source Target Value : Type*}

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

/-- The dynamic rank of a population member depends only on values on that
population. -/
theorem rankBy_congr_of_eqOn
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    {value value' : Particle → Value} (population : Finset Particle)
    {p : Particle} (hp : p ∈ population)
    (hvalue : ∀ q ∈ population, value q = value' q) :
    rankBy value population p = rankBy value' population p := by
  rw [rankBy_eq_card_filter, rankBy_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro q hq
  change (valueKey value q < valueKey value p) ↔
    (valueKey value' q < valueKey value' p)
  unfold valueKey
  rw [hvalue q hq, hvalue p hp]

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

/-- Equal-rank matching depends only on the values observed on the two finite
populations. -/
theorem matchByRankOrSelf_congr_of_eqOn
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    {sourceValue sourceValue' targetValue targetValue' : Particle → Value}
    (source target : Finset Particle) (hcard : source.card ≤ target.card)
    {p : Particle} (hp : p ∈ source)
    (hsource : ∀ q ∈ source, sourceValue q = sourceValue' q)
    (htarget : ∀ q ∈ target, targetValue q = targetValue' q) :
    matchByRankOrSelf sourceValue targetValue source target hcard p =
      matchByRankOrSelf sourceValue' targetValue' source target hcard p := by
  rw [matchByRankOrSelf_of_mem sourceValue targetValue source target hcard hp,
    matchByRankOrSelf_of_mem sourceValue' targetValue' source target hcard hp]
  apply rankBy_injOn targetValue' target
    (matchByRank_mem sourceValue targetValue source target hcard p hp)
    (matchByRank_mem sourceValue' targetValue' source target hcard p hp)
  have hleftMem := matchByRank_mem sourceValue targetValue source target
    hcard p hp
  have hrightMem := matchByRank_mem sourceValue' targetValue' source target
    hcard p hp
  calc
    rankBy targetValue' target
        (matchByRank sourceValue targetValue source target hcard p hp) =
      rankBy targetValue target
        (matchByRank sourceValue targetValue source target hcard p hp) :=
          (rankBy_congr_of_eqOn (value := targetValue)
            (value' := targetValue') target hleftMem htarget).symm
    _ = rankBy sourceValue source p :=
      rankBy_matchByRank sourceValue targetValue source target hcard p hp
    _ = rankBy sourceValue' source p :=
      rankBy_congr_of_eqOn (value := sourceValue)
        (value' := sourceValue') source hp hsource
    _ = rankBy targetValue' target
        (matchByRank sourceValue' targetValue' source target hcard p hp) :=
      (rankBy_matchByRank sourceValue' targetValue' source target hcard p hp).symm

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
