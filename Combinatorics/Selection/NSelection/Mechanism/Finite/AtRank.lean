/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Selection.NSelection.Mechanism.Finite.ByValue

/-!
# Recovering a finite candidate from its rank

Assume a linear order on candidate labels, and also on observed values for
the dynamic-value declarations below.

## Public declarations

- `Combinatorics.Selection.NSelection.existsUnique_rank_eq`: for
  $k<|s|$, there is a unique $p\in s$ with $\operatorname{rank}(s,p)=k$.
- `Combinatorics.Selection.NSelection.particleAtRank` returns the
  candidate of rank $k$ as an `Option`; its specification is given by
  `Combinatorics.Selection.NSelection.particleAtRank_eq_some_iff`,
  $\operatorname{particleAtRank}(s,k)=\operatorname{some}(p)\iff
  p\in s\land\operatorname{rank}(s,p)=k$, and
  `Combinatorics.Selection.NSelection.particleAtRank_eq_none_iff`,
  $\operatorname{particleAtRank}(s,k)=\operatorname{none}\iff |s|\le k$.
- `Combinatorics.Selection.NSelection.rankBy` ranks candidates by
  the observed-value key `(value, label)`.
  `Combinatorics.Selection.NSelection.rankBy_eq_card_filter` states
  $\operatorname{rankBy}(v,s,p)=
  |\{q\in s:K_v(q)<K_v(p)\}|$;
  `Combinatorics.Selection.NSelection.rankBy_lt_card_of_mem`
  bounds this rank by $|s|$ for $p\in s$;
  `Combinatorics.Selection.NSelection.rankBy_injOn` states that
  this rank is injective on $s$.
- `Combinatorics.Selection.NSelection.particleAtRankBy` returns the
  label at dynamic rank $k$. Its specifications are
  `Combinatorics.Selection.NSelection.particleAtRankBy_eq_some_iff`,
  $\operatorname{particleAtRankBy}(v,s,k)=\operatorname{some}(p)\iff
  p\in s\land\operatorname{rankBy}(v,s,p)=k$, and
  `Combinatorics.Selection.NSelection.particleAtRankBy_eq_none_iff`,
  which states that it is `none` exactly when $|s|\le k$.

- `Combinatorics.Selection.NSelection.valueAtRankBy` is the observed
  value at a selected rank, totalized by an explicit default value.
  `valueAtRankBy_eq_of_thresholdCounts` proves that two finite selections of
  equal size have the same observed value at each rank when all their lower-tail
  counts agree.

Here $K_v(p)$ denotes `valueKey v p`, so labels provide a deterministic
tie-break when two observed values agree.
-/

@[expose] public section

namespace Combinatorics.Selection.NSelection

variable {ι Value : Type*}

/-- Every valid rank is attained by exactly one member of the finite set. -/
theorem existsUnique_rank_eq [LinearOrder ι]
    (s : Finset ι) {k : ℕ} (hk : k < s.card) :
    ∃! p, p ∈ s ∧ rank s p = k := by
  have hkRange : k ∈ Finset.range s.card := Finset.mem_range.mpr hk
  rw [← image_rank_eq_range s] at hkRange
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hkRange
  refine ⟨p, ⟨hp, hpk⟩, ?_⟩
  intro q hq
  exact rank_injOn s hq.1 hp (hq.2.trans hpk.symm)

/-- The unique member of `s` having rank `k`, or `none` when `k` is outside
the rank range. -/
noncomputable def particleAtRank [LinearOrder ι]
    (s : Finset ι) (k : ℕ) : Option ι :=
  if hk : k < s.card then some (existsUnique_rank_eq s hk).choose else none

@[simp] theorem particleAtRank_eq_some_iff [LinearOrder ι]
    {s : Finset ι} {k : ℕ} {p : ι} :
    particleAtRank s k = some p ↔ p ∈ s ∧ rank s p = k := by
  classical
  by_cases hk : k < s.card
  · have hspec := (existsUnique_rank_eq s hk).choose_spec
    simp only [particleAtRank, dite_eq_left hk, Option.some.injEq]
    constructor
    · intro h
      simpa [← h] using hspec.1
    · intro hp
      exact (hspec.2 p hp).symm
  · simp only [particleAtRank, dite_eq_right hk]
    constructor
    · intro h
      cases h
    · intro hp
      exact (hk (hp.2 ▸ rank_lt_card_of_mem hp.1)).elim

@[simp] theorem particleAtRank_eq_none_iff [LinearOrder ι]
    {s : Finset ι} {k : ℕ} :
    particleAtRank s k = none ↔ s.card ≤ k := by
  classical
  by_cases hk : k < s.card
  · simp [particleAtRank, hk, Nat.not_le.mpr hk]
  · simp [particleAtRank, hk, Nat.le_of_not_gt hk]

/-- Rank after sorting candidates by observed value and using their labels
only to break ties. -/
noncomputable def rankBy [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (s : Finset ι) (p : ι) : ℕ :=
  rank (s.image (valueKey value)) (valueKey value p)

theorem rankBy_eq_card_filter [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (s : Finset ι) (p : ι) :
    rankBy value s p =
      (s.filter fun q => valueKey value q < valueKey value p).card := by
  unfold rankBy rank
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ (valueKey_injective value)

theorem rankBy_lt_card_of_mem [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) {s : Finset ι} {p : ι} (hp : p ∈ s) :
    rankBy value s p < s.card := by
  unfold rankBy
  rw [← Finset.card_image_of_injective s (valueKey_injective value)]
  exact rank_lt_card_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem rankBy_injOn [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (s : Finset ι) :
    Set.InjOn (rankBy value s) ↑s := by
  intro p hp q hq heq
  apply valueKey_injective value
  apply rank_injOn (s.image (valueKey value))
  · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  · exact heq

/-- The candidate of dynamic rank `k`, retaining the original label. -/
noncomputable def particleAtRankBy [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (s : Finset ι) (k : ℕ) : Option ι :=
  (particleAtRank (s.image (valueKey value)) k).map
    (fun key => (ofLex key).2)

@[simp] theorem particleAtRankBy_eq_some_iff
    [LinearOrder ι] [LinearOrder Value]
    {value : ι → Value} {s : Finset ι} {k : ℕ} {p : ι} :
    particleAtRankBy value s k = some p ↔
      p ∈ s ∧ rankBy value s p = k := by
  classical
  constructor
  · intro h
    obtain ⟨key, hkey, hlabel⟩ := Option.map_eq_some_iff.mp h
    have hkeySpec := particleAtRank_eq_some_iff.mp hkey
    obtain ⟨q, hq, hqkey⟩ := Finset.mem_image.mp hkeySpec.1
    subst key
    have hqp : q = p := by simpa using hlabel
    subst q
    exact ⟨hq, hkeySpec.2⟩
  · rintro ⟨hp, hrank⟩
    apply Option.map_eq_some_iff.mpr
    refine ⟨valueKey value p, ?_, rfl⟩
    exact particleAtRank_eq_some_iff.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hrank⟩

@[simp] theorem particleAtRankBy_eq_none_iff
    [LinearOrder ι] [LinearOrder Value]
    {value : ι → Value} {s : Finset ι} {k : ℕ} :
    particleAtRankBy value s k = none ↔ s.card ≤ k := by
  classical
  rw [particleAtRankBy, Option.map_eq_none_iff,
    particleAtRank_eq_none_iff,
    Finset.card_image_of_injective _ (valueKey_injective value)]

/-- The value at a prescribed rank in a finite selected set. The fallback is
irrelevant when the set has at least `k + 1` elements. -/
noncomputable def valueAtRankBy
    {ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (selected : Finset ι) (fallback : Value) (k : ℕ) : Value :=
  ((Combinatorics.Selection.NSelection.particleAtRankBy
    value selected k).map value).getD fallback

private lemma valueAtRankBy_threshold_bounds
    {ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (selected : Finset ι) (fallback : Value)
    {N k : ℕ} (hcard : selected.card = N) (hk : k < N) :
    (selected.filter fun q => value q < valueAtRankBy value selected fallback k).card ≤ k ∧
      k + 1 ≤ (selected.filter fun q =>
        value q ≤ valueAtRankBy value selected fallback k).card := by
  let opt := Combinatorics.Selection.NSelection.particleAtRankBy
    value selected k
  have hnotNone : opt ≠ none := by
    intro hnone
    have hle :=
      Combinatorics.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hnone
    omega
  obtain ⟨p, hpOpt⟩ := Option.ne_none_iff_exists.mp hnotNone
  have hpOpt' : opt = some p := hpOpt.symm
  have hp : p ∈ selected ∧
      Combinatorics.Selection.NSelection.rankBy value selected p = k :=
    Combinatorics.Selection.NSelection.particleAtRankBy_eq_some_iff.mp
      (by simpa [opt] using hpOpt')
  have hvalue : valueAtRankBy value selected fallback k = value p := by
    simp [valueAtRankBy, opt, hpOpt']
  have hkeyCard := hp.2
  unfold Combinatorics.Selection.NSelection.rankBy
    Combinatorics.Selection.NSelection.rank at hkeyCard
  rw [Finset.filter_image] at hkeyCard
  rw [Finset.card_image_of_injective _
    (Combinatorics.Selection.NSelection.valueKey_injective value)] at hkeyCard
  have hstrictSubset : (selected.filter fun q => value q < value p) ⊆
      selected.filter fun q =>
        Combinatorics.Selection.NSelection.valueKey value q <
          Combinatorics.Selection.NSelection.valueKey value p := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqin, hlt⟩
    exact Finset.mem_filter.mpr ⟨hqin, Prod.Lex.left q p hlt⟩
  have hstrictCard : (selected.filter fun q => value q < value p).card ≤ k := by
    calc
      (selected.filter fun q => value q < value p).card ≤
          (selected.filter fun q =>
            Combinatorics.Selection.NSelection.valueKey value q <
              Combinatorics.Selection.NSelection.valueKey value p).card :=
        Finset.card_le_card hstrictSubset
      _ = k := hkeyCard
  have hpNotKey : p ∉ selected.filter fun q =>
      Combinatorics.Selection.NSelection.valueKey value q <
        Combinatorics.Selection.NSelection.valueKey value p := by
    simp
  have hinsert : insert p (selected.filter fun q =>
      Combinatorics.Selection.NSelection.valueKey value q <
        Combinatorics.Selection.NSelection.valueKey value p) ⊆
      selected.filter fun q => value q ≤ value p := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hp.1, le_rfl⟩
    · rcases Finset.mem_filter.mp hq with ⟨hqin, hkey⟩
      have hle : value q ≤ value p := by
        change Prod.Lex (· < ·) (· < ·) (value q, q) (value p, p) at hkey
        rcases Prod.Lex.lt_iff.mp hkey with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact heq.le
      exact Finset.mem_filter.mpr ⟨hqin, hle⟩
  have hleCard : k + 1 ≤ (selected.filter fun q => value q ≤ value p).card := by
    calc
      k + 1 = (insert p (selected.filter fun q =>
          Combinatorics.Selection.NSelection.valueKey value q <
            Combinatorics.Selection.NSelection.valueKey value p)).card := by
        rw [Finset.card_insert_of_notMem hpNotKey, hkeyCard]
      _ ≤ (selected.filter fun q => value q ≤ value p).card :=
        Finset.card_le_card hinsert
  constructor
  · rw [hvalue]
    exact hstrictCard
  · rw [hvalue]
    exact hleCard

/-- Finite selections with the same counts below every value threshold have
the same value at each rank, even when their tie-breaking label orders differ. -/
theorem valueAtRankBy_eq_of_thresholdCounts
    {ι κ Value : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder Value]
    {N : ℕ} (valueLeft : ι → Value) (valueRight : κ → Value)
    (selectedLeft : Finset ι) (selectedRight : Finset κ)
    (fallbackLeft : Value) (fallbackRight : Value)
    (hcardLeft : selectedLeft.card = N) (hcardRight : selectedRight.card = N)
    (hcounts : ∀ a : Value,
      (selectedLeft.filter fun q => valueLeft q ≤ a).card =
        (selectedRight.filter fun q => valueRight q ≤ a).card)
    (i : Fin N) :
    valueAtRankBy valueLeft selectedLeft fallbackLeft i.val =
      valueAtRankBy valueRight selectedRight fallbackRight i.val := by
  have hleft := valueAtRankBy_threshold_bounds valueLeft selectedLeft fallbackLeft
    hcardLeft i.isLt
  have hright := valueAtRankBy_threshold_bounds valueRight selectedRight fallbackRight
    hcardRight i.isLt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcountLeft := hcounts
      (valueAtRankBy valueLeft selectedLeft fallbackLeft i.val)
    have hcountRightLe :
        (selectedRight.filter fun q => valueRight q ≤
          valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card ≤ i.val := by
      calc
        (selectedRight.filter fun q => valueRight q ≤
            valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card ≤
            (selectedRight.filter fun q => valueRight q <
              valueAtRankBy valueRight selectedRight fallbackRight i.val).card := by
          apply Finset.card_le_card
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
            lt_of_le_of_lt (Finset.mem_filter.mp hq).2 hlt⟩
        _ ≤ i.val := hright.1
    have hcountLeftGe : i.val + 1 ≤
        (selectedLeft.filter fun q => valueLeft q ≤
          valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card := hleft.2
    have hcontradiction : i.val + 1 ≤ i.val := by
      calc
        i.val + 1 ≤ (selectedLeft.filter fun q => valueLeft q ≤
            valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card :=
          hcountLeftGe
        _ = (selectedRight.filter fun q => valueRight q ≤
            valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card := hcountLeft
        _ ≤ i.val := hcountRightLe
    omega
  · have hcountRight := hcounts
      (valueAtRankBy valueRight selectedRight fallbackRight i.val)
    have hcountLeftLe :
        (selectedLeft.filter fun q => valueLeft q ≤
          valueAtRankBy valueRight selectedRight fallbackRight i.val).card ≤ i.val := by
      calc
        (selectedLeft.filter fun q => valueLeft q ≤
            valueAtRankBy valueRight selectedRight fallbackRight i.val).card ≤
            (selectedLeft.filter fun q => valueLeft q <
              valueAtRankBy valueLeft selectedLeft fallbackLeft i.val).card := by
          apply Finset.card_le_card
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
            lt_of_le_of_lt (Finset.mem_filter.mp hq).2 hgt⟩
        _ ≤ i.val := hleft.1
    have hcountRightGe : i.val + 1 ≤
        (selectedRight.filter fun q => valueRight q ≤
          valueAtRankBy valueRight selectedRight fallbackRight i.val).card := hright.2
    have hcontradiction : i.val + 1 ≤ i.val := by
      calc
        i.val + 1 ≤ (selectedRight.filter fun q => valueRight q ≤
            valueAtRankBy valueRight selectedRight fallbackRight i.val).card :=
          hcountRightGe
        _ = (selectedLeft.filter fun q => valueLeft q ≤
            valueAtRankBy valueRight selectedRight fallbackRight i.val).card := hcountRight.symm
        _ ≤ i.val := hcountLeftLe
    omega

end Combinatorics.Selection.NSelection

end
