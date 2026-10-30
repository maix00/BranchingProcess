/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Infinite.Basic
public import Combinatorics.Selection.NSelection.Mechanism.Finite.AtRank
/-!
# Equal-rank matching

Assume linear orders on the source labels, target labels, and values. The
## Public declarations

- `Combinatorics.Selection.NSelection.value_le_of_rankBy_eq_of_filter_card_le`:
  if every lower-tail count of the source is at most the corresponding target
  count, then equal dynamic ranks imply
  $\operatorname{targetValue}(q)\leq\operatorname{sourceValue}(p)$.
- `Combinatorics.Selection.NSelection.particleAtSourceRankBy`
  defines the optional target with the source particle's dynamic rank;
  `Combinatorics.Selection.NSelection.particleAtSourceRankBy_eq_some_iff`
  characterizes its value by target membership and rank equality.
  `Combinatorics.Selection.NSelection.preimageByRank` defines the
  membership-guarded optional inverse, and
  `Combinatorics.Selection.NSelection.preimageByRank_eq_some_iff`
  characterizes that inverse by membership and rank equality.
  `Combinatorics.Selection.NSelection.preimageByRank_leftUnique`
  proves that one source label has at most one target preimage.
- `Combinatorics.Selection.NSelection.particleAtSourceRankBy_ne_none`
  shows that each source member has a target at the same rank when
  $|\mathrm{source}|\leq|\mathrm{target}|$.
  `Combinatorics.Selection.NSelection.matchByRank` defines the
  resulting total match on source members;
  `Combinatorics.Selection.NSelection.particleAtSourceRankBy_matchByRank`
  identifies it with the optional construction,
  `Combinatorics.Selection.NSelection.matchByRank_mem` places its
  value in the target, and
  `Combinatorics.Selection.NSelection.rankBy_matchByRank` states
  equality of dynamic ranks.
  `Combinatorics.Selection.NSelection.particleAtSourceRankBy_matchByRank_target`
  states that looking up a source particle at the rank of its matched target
  recovers that source particle.
  `Combinatorics.Selection.NSelection.matchByRank_injective`
  proves injectivity, while
  `Combinatorics.Selection.NSelection.matchByRank_value_le` gives
  the value inequality under lower-tail count domination.
- `Combinatorics.Selection.NSelection.rankBy_congr_of_eqOn` states
  $\operatorname{rankBy}(f,S,p)=\operatorname{rankBy}(f',S,p)$ when
  $p\in S$ and $f=f'$ on $S$.
  `Combinatorics.Selection.NSelection.matchByRankOrSelf`
  defines the ambient extension that fixes labels outside the source;
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_of_mem`
  and
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_of_not_mem`
  give its two defining cases.
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_congr_of_eqOn`
  proves invariance under value-function changes off the two populations,
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_mem` maps
  source members into the target, and
  `Combinatorics.Selection.NSelection.particleAtSourceRankBy_matchByRankOrSelf`
  gives the inverse identity on the source.
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_injOn`
  proves injectivity on the source, and
  `Combinatorics.Selection.NSelection.matchByRankOrSelf_value_le`
  gives the lower-tail value bound there.

- `Combinatorics.Selection.NSelection.firstNBy_value_thresholdCounts_eq_of_bijectiveCandidates`:
  a value-preserving bijection between candidate populations identifies the
  lower-tail counts of their first-$N$ selections.

The existence results from finite Hall matching are in
`NSelection/Matching/Hall.lean`.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

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

/-- Two first-`N` selections have the same value-threshold counts when their
candidate sets are in value-preserving bijection. This converts an address
relabeling into the hypothesis of `valueAtRankBy_eq_of_thresholdCounts`.
-/
theorem firstNBy_value_thresholdCounts_eq_of_bijectiveCandidates
    {ι κ Value : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder Value]
    {N : ℕ} (valueLeft : ι → Value) (valueRight : κ → Value)
    (candidatesLeft : Set ι) (candidatesRight : Set κ)
    (selectedLeft : Finset ι) (selectedRight : Finset κ)
    (hselectedLeft : Combinatorics.Selection.NSelection.IsFirstNBy
      N valueLeft candidatesLeft selectedLeft)
    (hselectedRight : Combinatorics.Selection.NSelection.IsFirstNBy
      N valueRight candidatesRight selectedRight)
    (hcardLeft : selectedLeft.card = N) (hcardRight : selectedRight.card = N)
    (forward : κ → ι) (backward : ι → κ)
    (hforward : ∀ q ∈ candidatesRight, forward q ∈ candidatesLeft)
    (hbackward : ∀ p ∈ candidatesLeft, backward p ∈ candidatesRight)
    (hbackwardForward : ∀ p ∈ candidatesLeft, forward (backward p) = p)
    (hforwardBackward : ∀ q ∈ candidatesRight, backward (forward q) = q)
    (hvalue : ∀ q ∈ candidatesRight, valueLeft (forward q) = valueRight q)
    (a : Value) :
    (selectedLeft.filter fun p => valueLeft p ≤ a).card =
      (selectedRight.filter fun q => valueRight q ≤ a).card := by
  let mappedRight := selectedRight.image forward
  have hforwardInjective : Set.InjOn forward (↑selectedRight : Set κ) := by
    intro q hq r hr hqr
    calc
      q = backward (forward q) := (hforwardBackward q (hselectedRight.subset hq)).symm
      _ = backward (forward r) := congrArg backward hqr
      _ = r := hforwardBackward r (hselectedRight.subset hr)
  have hmappedRightSubset : (↑mappedRight : Set ι) ⊆ candidatesLeft := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hforward q (hselectedRight.subset hq)
  have hmappedRightCard : mappedRight.card = N := by
    rw [Finset.card_image_iff.mpr hforwardInjective, hcardRight]
  have hrightFilterImage :
      (mappedRight.filter fun p => valueLeft p ≤ a) =
        (selectedRight.filter fun q => valueRight q ≤ a).image forward := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpimage, hpvalue⟩
      rcases Finset.mem_image.mp hpimage with ⟨q, hq, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, rfl⟩
      simpa [hvalue q (hselectedRight.subset hq)] using hpvalue
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hqfilter, rfl⟩
      rcases Finset.mem_filter.mp hqfilter with ⟨hq, hqvalue⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
      simpa [hvalue q (hselectedRight.subset hq)] using hqvalue
  have hrightFilterCard :
      (mappedRight.filter fun p => valueLeft p ≤ a).card =
        (selectedRight.filter fun q => valueRight q ≤ a).card := by
    have hinj : Set.InjOn forward
        (↑(selectedRight.filter fun q => valueRight q ≤ a) : Set κ) := by
      intro q hq r hr hqr
      exact hforwardInjective (Finset.mem_filter.mp hq).1
        (Finset.mem_filter.mp hr).1 hqr
    rw [hrightFilterImage, Finset.card_image_iff.mpr hinj]
  have hrightLe :
      (selectedRight.filter fun q => valueRight q ≤ a).card ≤
        (selectedLeft.filter fun p => valueLeft p ≤ a).card := by
    calc
      _ = (mappedRight.filter fun p => valueLeft p ≤ a).card := hrightFilterCard.symm
      _ ≤ (selectedLeft.filter fun p => valueLeft p ≤ a).card := by
        exact Combinatorics.Selection.NSelection.filter_card_le_filter_of_isFirstNBy
          N valueLeft candidatesLeft selectedLeft mappedRight hselectedLeft
          hmappedRightSubset (by simpa only [hmappedRightCard] using Nat.le_refl N) a
  have hvalueBackward : ∀ p ∈ candidatesLeft,
      valueRight (backward p) = valueLeft p := by
    intro p hp
    have hback := hbackward p hp
    calc
      valueRight (backward p) = valueLeft (forward (backward p)) :=
        (hvalue (backward p) hback).symm
      _ = valueLeft p := congrArg valueLeft (hbackwardForward p hp)
  let mappedLeft := selectedLeft.image backward
  have hbackwardInjective : Set.InjOn backward (↑selectedLeft : Set ι) := by
    intro p hp q hq hpq
    calc
      p = forward (backward p) := (hbackwardForward p (hselectedLeft.subset hp)).symm
      _ = forward (backward q) := congrArg forward hpq
      _ = q := hbackwardForward q (hselectedLeft.subset hq)
  have hmappedLeftSubset : (↑mappedLeft : Set κ) ⊆ candidatesRight := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hbackward p (hselectedLeft.subset hp)
  have hmappedLeftCard : mappedLeft.card = N := by
    rw [Finset.card_image_iff.mpr hbackwardInjective, hcardLeft]
  have hleftFilterImage :
      (mappedLeft.filter fun q => valueRight q ≤ a) =
        (selectedLeft.filter fun p => valueLeft p ≤ a).image backward := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqimage, hqvalue⟩
      rcases Finset.mem_image.mp hqimage with ⟨p, hp, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      simpa [hvalueBackward p (hselectedLeft.subset hp)] using hqvalue
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨p, hpfilter, rfl⟩
      rcases Finset.mem_filter.mp hpfilter with ⟨hp, hpvalue⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      simpa [hvalueBackward p (hselectedLeft.subset hp)] using hpvalue
  have hleftFilterCard :
      (mappedLeft.filter fun q => valueRight q ≤ a).card =
        (selectedLeft.filter fun p => valueLeft p ≤ a).card := by
    have hinj : Set.InjOn backward
        (↑(selectedLeft.filter fun p => valueLeft p ≤ a) : Set ι) := by
      intro p hp q hq hpq
      exact hbackwardInjective (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hq).1 hpq
    rw [hleftFilterImage, Finset.card_image_iff.mpr hinj]
  have hleftLe :
      (selectedLeft.filter fun p => valueLeft p ≤ a).card ≤
        (selectedRight.filter fun q => valueRight q ≤ a).card := by
    calc
      _ = (mappedLeft.filter fun q => valueRight q ≤ a).card := hleftFilterCard.symm
      _ ≤ (selectedRight.filter fun q => valueRight q ≤ a).card := by
        exact Combinatorics.Selection.NSelection.filter_card_le_filter_of_isFirstNBy
          N valueRight candidatesRight selectedRight mappedLeft hselectedRight
          hmappedLeftSubset (by simpa only [hmappedLeftCard] using Nat.le_refl N) a
  exact Nat.le_antisymm hleftLe hrightLe

end Combinatorics.Selection.NSelection
