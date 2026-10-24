/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Mechanism.ByValue

/-!
# Recovering a finite candidate from its rank

Assume a linear order on candidate labels, and also on observed values for
the dynamic-value declarations below. The public declarations are:

- `Combinatorics.Branching.Selection.NSelection.existsUnique_rank_eq`: for
  $k<|s|$, there is a unique $p\in s$ with $\operatorname{rank}(s,p)=k$.
- `Combinatorics.Branching.Selection.NSelection.particleAtRank` returns the
  candidate of rank $k$ as an `Option`; its specification is given by
  `Combinatorics.Branching.Selection.NSelection.particleAtRank_eq_some_iff`,
  $\operatorname{particleAtRank}(s,k)=\operatorname{some}(p)\iff
  p\in s\land\operatorname{rank}(s,p)=k$, and
  `Combinatorics.Branching.Selection.NSelection.particleAtRank_eq_none_iff`,
  $\operatorname{particleAtRank}(s,k)=\operatorname{none}\iff |s|\le k$.
- `Combinatorics.Branching.Selection.NSelection.rankBy` ranks candidates by
  the observed-value key `(value, label)`.
  `Combinatorics.Branching.Selection.NSelection.rankBy_eq_card_filter` states
  $\operatorname{rankBy}(v,s,p)=
  |\{q\in s:K_v(q)<K_v(p)\}|$;
  `Combinatorics.Branching.Selection.NSelection.rankBy_lt_card_of_mem`
  bounds this rank by $|s|$ for $p\in s$;
  `Combinatorics.Branching.Selection.NSelection.rankBy_injOn` states that
  this rank is injective on $s$.
- `Combinatorics.Branching.Selection.NSelection.particleAtRankBy` returns the
  label at dynamic rank $k$. Its specifications are
  `Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff`,
  $\operatorname{particleAtRankBy}(v,s,k)=\operatorname{some}(p)\iff
  p\in s\land\operatorname{rankBy}(v,s,p)=k$, and
  `Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff`,
  which states that it is `none` exactly when $|s|\le k$.

Here $K_v(p)$ denotes `valueKey v p`, so labels provide a deterministic
tie-break when two observed values agree.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

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


end Combinatorics.Branching.Selection.NSelection

end
