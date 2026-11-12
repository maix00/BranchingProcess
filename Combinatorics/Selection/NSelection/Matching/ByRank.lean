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

This file matches a finite set `objectsToMatch` into a finite set
`availablePartners` by equal dynamic rank. The two sets may have different
label types, and each has an order-key map.

## Public declarations

- `Combinatorics.Selection.NSelection.partnerOrderKey_le_of_rankBy_eq_of_filter_card_le`:
  if every threshold count of `objectsToMatch` is at most the corresponding
  count for `availablePartners`, equal dynamic ranks give
  $\operatorname{partnerOrderKey}(y)\leq\operatorname{objectOrderKey}(x)$.
- `Combinatorics.Selection.NSelection.partnerAtObjectRankBy` defines the
  optional partner at an object's dynamic rank. Its `_eq_some_iff` theorem
  characterizes the result by membership in `availablePartners` and rank
  equality. `objectAtPartnerRankBy` defines the membership-guarded inverse;
  its `_eq_some_iff` theorem characterizes that inverse, and
  `objectAtPartnerRankBy_leftUnique` proves uniqueness of an object matched
  to a given partner.
- `Combinatorics.Selection.NSelection.partnerAtObjectRankBy_ne_none` shows
  that every object in `objectsToMatch` has a same-rank partner when
  $|\mathrm{objectsToMatch}|\leq|\mathrm{availablePartners}|$.
  `Combinatorics.Selection.NSelection.matchByRank` defines the resulting
  total match on `objectsToMatch`; `partnerAtObjectRankBy_matchByRank`
  identifies it with the optional construction, `matchByRank_mem` places each
  result in `availablePartners`, and `rankBy_matchByRank` states equality of
  dynamic ranks. `partnerAtObjectRankBy_matchByRank_partner` states that the
  inverse lookup at the matched partner recovers the original object.
  `matchByRank_injective` proves injectivity, while
  `matchByRank_partnerOrderKey_le` gives the order-key inequality under
  threshold-count domination.
- `Combinatorics.Selection.NSelection.rankBy_congr_of_eqOn` states
  $\operatorname{rankBy}(f,S,x)=\operatorname{rankBy}(f',S,x)$ when
  $x\in S$ and $f=f'$ on $S$.
  `Combinatorics.Selection.NSelection.matchByRankOrSelf` defines the ambient
  extension that fixes labels outside `objectsToMatch`;
  `matchByRankOrSelf_of_mem` and `matchByRankOrSelf_of_not_mem` give its two
  defining cases. `matchByRankOrSelf_congr_of_eqOn` proves invariance under
  order-key changes off the two sets; `matchByRankOrSelf_mem` maps objects of
  `objectsToMatch` into `availablePartners`, and
  `partnerAtObjectRankBy_matchByRankOrSelf` gives the inverse identity on
  `objectsToMatch`. `matchByRankOrSelf_injOn` proves injectivity there, and
  `matchByRankOrSelf_partnerOrderKey_le` gives the threshold-count order-key bound.
- `Combinatorics.Selection.NSelection.firstNBy_orderKey_thresholdCounts_eq_of_bijectivePartnerSets`:
  an order-key-preserving bijection between two available-partner sets identifies the
  threshold counts of their first-$N$ selections.

The existence results from finite Hall matching are in
`NSelection/Matching/SelectedPopulation.lean`.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

variable {Object Partner OrderKey : Type*}

/-- Threshold-count domination gives the partner order-key bound at equal
dynamic rank. This is the deterministic core of the canonical rank matching. -/
theorem partnerOrderKey_le_of_rankBy_eq_of_filter_card_le
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hthreshold : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card)
    {p : Object} (hp : p ∈ objectsToMatch) {q : Partner}
    (hrank : rankBy partnerOrderKey availablePartners q =
      rankBy objectOrderKey objectsToMatch p) :
    partnerOrderKey q ≤ objectOrderKey p := by
  by_contra hle
  have hlt : objectOrderKey p < partnerOrderKey q := lt_of_not_ge hle
  let objectsToMatchBelow := objectsToMatch.filter fun r =>
    valueKey objectOrderKey r < valueKey objectOrderKey p
  let availablePartnersBelow := availablePartners.filter fun r =>
    valueKey partnerOrderKey r < valueKey partnerOrderKey q
  have hpNotBelow : p ∉ objectsToMatchBelow := by
    simp [objectsToMatchBelow]
  have hobjectsToMatchSubset : insert p objectsToMatchBelow ⊆
      objectsToMatch.filter fun r => objectOrderKey r ≤ objectOrderKey p := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_filter.mpr ⟨hp, le_rfl⟩
    · obtain ⟨hrs, hrkey⟩ := Finset.mem_filter.mp hr
      have hrOrderKey : objectOrderKey r ≤ objectOrderKey p := by
        rcases Prod.Lex.lt_iff.mp hrkey with h | h
        · exact le_of_lt h
        · exact le_of_eq h.1
      exact Finset.mem_filter.mpr ⟨hrs, hrOrderKey⟩
  have havailablePartnersSubset :
      availablePartners.filter (fun r => partnerOrderKey r ≤ objectOrderKey p) ⊆ availablePartnersBelow := by
    intro r hr
    obtain ⟨hrt, hrOrderKey⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr
      ⟨hrt, valueKey_lt_of_value_lt partnerOrderKey (hrOrderKey.trans_lt hlt)⟩
  have hobjectsToMatchCard : rankBy objectOrderKey objectsToMatch p + 1 ≤
      (objectsToMatch.filter fun r => objectOrderKey r ≤ objectOrderKey p).card := by
    rw [rankBy_eq_card_filter]
    change objectsToMatchBelow.card + 1 ≤ _
    rw [← Finset.card_insert_of_notMem hpNotBelow]
    exact Finset.card_le_card hobjectsToMatchSubset
  have havailablePartnersCard :
      (availablePartners.filter fun r => partnerOrderKey r ≤ objectOrderKey p).card ≤
        rankBy partnerOrderKey availablePartners q := by
    rw [rankBy_eq_card_filter]
    exact Finset.card_le_card havailablePartnersSubset
  have hcount := hthreshold (objectOrderKey p)
  omega

/-- Return the available partner at an object's dynamic rank, when that rank
is attained in `availablePartners`. -/
noncomputable def partnerAtObjectRankBy
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner) (p : Object) :
    Option Partner :=
  particleAtRankBy partnerOrderKey availablePartners (rankBy objectOrderKey objectsToMatch p)

@[simp] theorem partnerAtObjectRankBy_eq_some_iff
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    {objectOrderKey : Object → OrderKey} {partnerOrderKey : Partner → OrderKey}
    {objectsToMatch : Finset Object} {availablePartners : Finset Partner}
    {p : Object} {q : Partner} :
    partnerAtObjectRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners p = some q ↔
      q ∈ availablePartners ∧ rankBy partnerOrderKey availablePartners q =
        rankBy objectOrderKey objectsToMatch p := by
  exact particleAtRankBy_eq_some_iff

/-- Return the object at a partner's dynamic rank, when the partner belongs to
`availablePartners`. The membership guard ensures that an outside label with
the same rank does not duplicate an object. -/
noncomputable def objectAtPartnerRankBy
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner) (q : Partner) :
    Option Object :=
  if q ∈ availablePartners then
    partnerAtObjectRankBy partnerOrderKey objectOrderKey availablePartners objectsToMatch q
  else none

@[simp] theorem objectAtPartnerRankBy_eq_some_iff
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    {objectOrderKey : Object → OrderKey} {partnerOrderKey : Partner → OrderKey}
    {objectsToMatch : Finset Object} {availablePartners : Finset Partner}
    {q : Partner} {p : Object} :
    objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners q = some p ↔
      q ∈ availablePartners ∧ p ∈ objectsToMatch ∧
        rankBy objectOrderKey objectsToMatch p = rankBy partnerOrderKey availablePartners q := by
  by_cases hq : q ∈ availablePartners
  · simp only [objectAtPartnerRankBy, hq, ↓reduceIte,
      partnerAtObjectRankBy_eq_some_iff]
    tauto
  · simp [objectAtPartnerRankBy, hq]

/-- The inverse equal-rank match uses each object at most once. -/
theorem objectAtPartnerRankBy_leftUnique
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    {q₁ q₂ : Partner} {p : Object}
    (h₁ : objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners q₁ = some p)
    (h₂ : objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners q₂ = some p) :
    q₁ = q₂ := by
  obtain ⟨hq₁, _, hr₁⟩ := objectAtPartnerRankBy_eq_some_iff.mp h₁
  obtain ⟨hq₂, _, hr₂⟩ := objectAtPartnerRankBy_eq_some_iff.mp h₂
  apply rankBy_injOn partnerOrderKey availablePartners hq₁ hq₂
  exact hr₁.symm.trans hr₂

/-- Every object in `objectsToMatch` has a same-rank partner when
`availablePartners` has at least as many elements. -/
theorem partnerAtObjectRankBy_ne_none
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    {objectsToMatch : Finset Object} {availablePartners : Finset Partner}
    {p : Object} (hp : p ∈ objectsToMatch) (hcard : objectsToMatch.card ≤ availablePartners.card) :
    partnerAtObjectRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners p ≠ none := by
  intro hnone
  have hle : availablePartners.card ≤ rankBy objectOrderKey objectsToMatch p :=
    particleAtRankBy_eq_none_iff.mp hnone
  exact (not_le_of_gt ((rankBy_lt_card_of_mem objectOrderKey hp).trans_le hcard)) hle

/-- The partner having the same dynamic rank as an object in `objectsToMatch`.

The membership proof is an argument because existence only follows on the
objectsToMatch set.  This avoids adding an arbitrary default element to either
ambient type. -/
noncomputable def matchByRank
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Object) (hp : p ∈ objectsToMatch) : Partner :=
  Option.get
    (partnerAtObjectRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners p)
    (Option.isSome_iff_ne_none.mpr
      (partnerAtObjectRankBy_ne_none objectOrderKey partnerOrderKey hp hcard))

theorem partnerAtObjectRankBy_matchByRank
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Object) (hp : p ∈ objectsToMatch) :
    partnerAtObjectRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners p =
      some (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) := by
  unfold matchByRank
  exact (Option.some_get _).symm

theorem matchByRank_mem
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Object) (hp : p ∈ objectsToMatch) :
    matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp ∈ availablePartners := by
  exact (partnerAtObjectRankBy_eq_some_iff.mp
    (partnerAtObjectRankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners
      hcard p hp)).1

/-- The dynamic rank of an element depends only on its order key on the
population. -/
theorem rankBy_congr_of_eqOn
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    {orderKey orderKey' : Element → OrderKey} (population : Finset Element)
    {p : Element} (hp : p ∈ population)
    (horderKey : ∀ q ∈ population, orderKey q = orderKey' q) :
    rankBy orderKey population p = rankBy orderKey' population p := by
  rw [rankBy_eq_card_filter, rankBy_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro q hq
  change (valueKey orderKey q < valueKey orderKey p) ↔
    (valueKey orderKey' q < valueKey orderKey' p)
  unfold valueKey
  rw [horderKey q hq, horderKey p hp]

theorem rankBy_matchByRank
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Object) (hp : p ∈ objectsToMatch) :
    rankBy partnerOrderKey availablePartners
        (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) =
      rankBy objectOrderKey objectsToMatch p := by
  exact (partnerAtObjectRankBy_eq_some_iff.mp
    (partnerAtObjectRankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners
      hcard p hp)).2

/-- Looking up an object at the dynamic rank of its matched partner recovers
that object. -/
theorem partnerAtObjectRankBy_matchByRank_partner
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Object) (hp : p ∈ objectsToMatch) :
    partnerAtObjectRankBy partnerOrderKey objectOrderKey availablePartners objectsToMatch
        (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) =
      some p := by
  apply partnerAtObjectRankBy_eq_some_iff.mpr
  exact ⟨hp,
    (rankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp).symm⟩

/-- Equal-rank matching is injective on the objectsToMatch subtype. -/
theorem matchByRank_injective
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card) :
    Function.Injective fun p : {p // p ∈ objectsToMatch} =>
      matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p.1 p.2 := by
  intro p q heq
  apply Subtype.ext
  apply rankBy_injOn objectOrderKey objectsToMatch p.2 q.2
  change matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p.1 p.2 =
    matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard q.1 q.2 at heq
  rw [← rankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p.1 p.2,
    ← rankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard q.1 q.2]
  exact congrArg (rankBy partnerOrderKey availablePartners) heq

/-- Threshold-count domination makes equal-rank matching nonincreasing in
the order key. -/
theorem matchByRank_partnerOrderKey_le
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hcard : objectsToMatch.card ≤ availablePartners.card)
    (hthreshold : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card)
    (p : Object) (hp : p ∈ objectsToMatch) :
    partnerOrderKey (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) ≤
      objectOrderKey p := by
  apply partnerOrderKey_le_of_rankBy_eq_of_filter_card_le objectOrderKey partnerOrderKey
    objectsToMatch availablePartners hthreshold hp
  exact rankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp

/-- Extend equal-rank matching to the ambient type by fixing labels outside
`objectsToMatch`. -/
noncomputable def matchByRankOrSelf
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    (p : Element) : Element :=
  if hp : p ∈ objectsToMatch then
    matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp
  else p

@[simp] theorem matchByRankOrSelf_of_mem
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    {p : Element} (hp : p ∈ objectsToMatch) :
    matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p =
      matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp := by
  simp [matchByRankOrSelf, hp]

/-- Equal-rank matching depends only on the order keys on the two finite
sets. -/
theorem matchByRankOrSelf_congr_of_eqOn
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    {objectOrderKey objectOrderKey' partnerOrderKey partnerOrderKey' : Element → OrderKey}
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    {p : Element} (hp : p ∈ objectsToMatch)
    (hobjectOrderKeyEq : ∀ q ∈ objectsToMatch, objectOrderKey q = objectOrderKey' q)
    (hpartnerOrderKeyEq : ∀ q ∈ availablePartners, partnerOrderKey q = partnerOrderKey' q) :
    matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p =
      matchByRankOrSelf objectOrderKey' partnerOrderKey' objectsToMatch availablePartners hcard p := by
  rw [matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hp,
    matchByRankOrSelf_of_mem objectOrderKey' partnerOrderKey' objectsToMatch availablePartners hcard hp]
  apply rankBy_injOn partnerOrderKey' availablePartners
    (matchByRank_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp)
    (matchByRank_mem objectOrderKey' partnerOrderKey' objectsToMatch availablePartners hcard p hp)
  have hleftMem := matchByRank_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners
    hcard p hp
  have hrightMem := matchByRank_mem objectOrderKey' partnerOrderKey' objectsToMatch availablePartners
    hcard p hp
  calc
    rankBy partnerOrderKey' availablePartners
        (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) =
      rankBy partnerOrderKey availablePartners
        (matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp) :=
          (rankBy_congr_of_eqOn (orderKey := partnerOrderKey)
            (orderKey' := partnerOrderKey') availablePartners hleftMem hpartnerOrderKeyEq).symm
    _ = rankBy objectOrderKey objectsToMatch p :=
      rankBy_matchByRank objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp
    _ = rankBy objectOrderKey' objectsToMatch p :=
      rankBy_congr_of_eqOn (orderKey := objectOrderKey)
        (orderKey' := objectOrderKey') objectsToMatch hp hobjectOrderKeyEq
    _ = rankBy partnerOrderKey' availablePartners
        (matchByRank objectOrderKey' partnerOrderKey' objectsToMatch availablePartners hcard p hp) :=
      (rankBy_matchByRank objectOrderKey' partnerOrderKey' objectsToMatch availablePartners hcard p hp).symm

@[simp] theorem matchByRankOrSelf_of_not_mem
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    {p : Element} (hp : p ∉ objectsToMatch) :
    matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p = p := by
  simp [matchByRankOrSelf, hp]

theorem matchByRankOrSelf_mem
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    {p : Element} (hp : p ∈ objectsToMatch) :
    matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p ∈ availablePartners := by
  rw [matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hp]
  exact matchByRank_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p hp

/-- On `objectsToMatch`, the optional inverse recovers the ambient equal-rank
match. -/
theorem partnerAtObjectRankBy_matchByRankOrSelf
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    {p : Element} (hp : p ∈ objectsToMatch) :
    partnerAtObjectRankBy partnerOrderKey objectOrderKey availablePartners objectsToMatch
        (matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p) =
      some p := by
  rw [matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hp]
  exact partnerAtObjectRankBy_matchByRank_partner objectOrderKey partnerOrderKey
    objectsToMatch availablePartners hcard p hp

theorem matchByRankOrSelf_injOn
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card) :
    Set.InjOn (matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard)
      ↑objectsToMatch := by
  intro p hp q hq heq
  have hp' : p ∈ objectsToMatch := hp
  have hq' : q ∈ objectsToMatch := hq
  have hsub : (⟨p, hp⟩ : {p // p ∈ objectsToMatch}) = ⟨q, hq⟩ := by
    apply matchByRank_injective objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard
    rw [matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hp',
      matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hq'] at heq
    exact heq
  exact congrArg Subtype.val hsub

theorem matchByRankOrSelf_partnerOrderKey_le
    {Element : Type*} [LinearOrder Element] [LinearOrder OrderKey]
    (objectOrderKey partnerOrderKey : Element → OrderKey)
    (objectsToMatch availablePartners : Finset Element) (hcard : objectsToMatch.card ≤ availablePartners.card)
    (hthreshold : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card)
    {p : Element} (hp : p ∈ objectsToMatch) :
    partnerOrderKey
        (matchByRankOrSelf objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard p) ≤
      objectOrderKey p := by
  rw [matchByRankOrSelf_of_mem objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard hp]
  exact matchByRank_partnerOrderKey_le objectOrderKey partnerOrderKey objectsToMatch availablePartners hcard
    hthreshold p hp

/-- Two first-`N` selections have the same order-key threshold counts when
their available-partner sets are in order-key-preserving bijection. This
converts an address relabeling into the hypothesis of
`valueAtRankBy_eq_of_thresholdCounts`.
-/
theorem firstNBy_orderKey_thresholdCounts_eq_of_bijectivePartnerSets
    {ι κ OrderKey : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder OrderKey]
    {N : ℕ} (partnerOrderKeyLeft : ι → OrderKey) (partnerOrderKeyRight : κ → OrderKey)
    (availablePartnersLeft : Set ι) (availablePartnersRight : Set κ)
    (selectedPartnersLeft : Finset ι) (selectedPartnersRight : Finset κ)
    (hselectedLeft : Combinatorics.Selection.NSelection.IsFirstNBy
      N partnerOrderKeyLeft availablePartnersLeft selectedPartnersLeft)
    (hselectedRight : Combinatorics.Selection.NSelection.IsFirstNBy
      N partnerOrderKeyRight availablePartnersRight selectedPartnersRight)
    (hcardLeft : selectedPartnersLeft.card = N) (hcardRight : selectedPartnersRight.card = N)
    (forward : κ → ι) (backward : ι → κ)
    (hforward : ∀ q ∈ availablePartnersRight, forward q ∈ availablePartnersLeft)
    (hbackward : ∀ p ∈ availablePartnersLeft, backward p ∈ availablePartnersRight)
    (hbackwardForward : ∀ p ∈ availablePartnersLeft, forward (backward p) = p)
    (hforwardBackward : ∀ q ∈ availablePartnersRight, backward (forward q) = q)
    (horderKey : ∀ q ∈ availablePartnersRight, partnerOrderKeyLeft (forward q) = partnerOrderKeyRight q)
    (a : OrderKey) :
    (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).card =
      (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).card := by
  let mappedRight := selectedPartnersRight.image forward
  have hforwardInjective : Set.InjOn forward (↑selectedPartnersRight : Set κ) := by
    intro q hq r hr hqr
    calc
      q = backward (forward q) := (hforwardBackward q (hselectedRight.subset hq)).symm
      _ = backward (forward r) := congrArg backward hqr
      _ = r := hforwardBackward r (hselectedRight.subset hr)
  have hmappedRightSubset : (↑mappedRight : Set ι) ⊆ availablePartnersLeft := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hforward q (hselectedRight.subset hq)
  have hmappedRightCard : mappedRight.card = N := by
    rw [Finset.card_image_iff.mpr hforwardInjective, hcardRight]
  have hrightFilterImage :
      (mappedRight.filter fun p => partnerOrderKeyLeft p ≤ a) =
        (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).image forward := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpimage, hpOrderKey⟩
      rcases Finset.mem_image.mp hpimage with ⟨q, hq, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, rfl⟩
      simpa [horderKey q (hselectedRight.subset hq)] using hpOrderKey
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hqfilter, rfl⟩
      rcases Finset.mem_filter.mp hqfilter with ⟨hq, hqOrderKey⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
      simpa [horderKey q (hselectedRight.subset hq)] using hqOrderKey
  have hrightFilterCard :
      (mappedRight.filter fun p => partnerOrderKeyLeft p ≤ a).card =
        (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).card := by
    have hinj : Set.InjOn forward
        (↑(selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a) : Set κ) := by
      intro q hq r hr hqr
      exact hforwardInjective (Finset.mem_filter.mp hq).1
        (Finset.mem_filter.mp hr).1 hqr
    rw [hrightFilterImage, Finset.card_image_iff.mpr hinj]
  have hrightLe :
      (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).card ≤
        (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).card := by
    calc
      _ = (mappedRight.filter fun p => partnerOrderKeyLeft p ≤ a).card := hrightFilterCard.symm
      _ ≤ (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).card := by
        exact Combinatorics.Selection.NSelection.filter_card_le_filter_of_isFirstNBy
          N partnerOrderKeyLeft availablePartnersLeft selectedPartnersLeft mappedRight hselectedLeft
          hmappedRightSubset (by simpa only [hmappedRightCard] using Nat.le_refl N) a
  have hpartnerOrderKeyBackward : ∀ p ∈ availablePartnersLeft,
      partnerOrderKeyRight (backward p) = partnerOrderKeyLeft p := by
    intro p hp
    have hback := hbackward p hp
    calc
      partnerOrderKeyRight (backward p) = partnerOrderKeyLeft (forward (backward p)) :=
        (horderKey (backward p) hback).symm
      _ = partnerOrderKeyLeft p := congrArg partnerOrderKeyLeft (hbackwardForward p hp)
  let mappedLeft := selectedPartnersLeft.image backward
  have hbackwardInjective : Set.InjOn backward (↑selectedPartnersLeft : Set ι) := by
    intro p hp q hq hpq
    calc
      p = forward (backward p) := (hbackwardForward p (hselectedLeft.subset hp)).symm
      _ = forward (backward q) := congrArg forward hpq
      _ = q := hbackwardForward q (hselectedLeft.subset hq)
  have hmappedLeftSubset : (↑mappedLeft : Set κ) ⊆ availablePartnersRight := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hbackward p (hselectedLeft.subset hp)
  have hmappedLeftCard : mappedLeft.card = N := by
    rw [Finset.card_image_iff.mpr hbackwardInjective, hcardLeft]
  have hleftFilterImage :
      (mappedLeft.filter fun q => partnerOrderKeyRight q ≤ a) =
        (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).image backward := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hqimage, hqOrderKey⟩
      rcases Finset.mem_image.mp hqimage with ⟨p, hp, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      simpa [hpartnerOrderKeyBackward p (hselectedLeft.subset hp)] using hqOrderKey
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨p, hpfilter, rfl⟩
      rcases Finset.mem_filter.mp hpfilter with ⟨hp, hpOrderKey⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      simpa [hpartnerOrderKeyBackward p (hselectedLeft.subset hp)] using hpOrderKey
  have hleftFilterCard :
      (mappedLeft.filter fun q => partnerOrderKeyRight q ≤ a).card =
        (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).card := by
    have hinj : Set.InjOn backward
        (↑(selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a) : Set ι) := by
      intro p hp q hq hpq
      exact hbackwardInjective (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hq).1 hpq
    rw [hleftFilterImage, Finset.card_image_iff.mpr hinj]
  have hleftLe :
      (selectedPartnersLeft.filter fun p => partnerOrderKeyLeft p ≤ a).card ≤
        (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).card := by
    calc
      _ = (mappedLeft.filter fun q => partnerOrderKeyRight q ≤ a).card := hleftFilterCard.symm
      _ ≤ (selectedPartnersRight.filter fun q => partnerOrderKeyRight q ≤ a).card := by
        exact Combinatorics.Selection.NSelection.filter_card_le_filter_of_isFirstNBy
          N partnerOrderKeyRight availablePartnersRight selectedPartnersRight mappedLeft hselectedRight
          hmappedLeftSubset (by simpa only [hmappedLeftCard] using Nat.le_refl N) a
  exact Nat.le_antisymm hleftLe hrightLe

end Combinatorics.Selection.NSelection
