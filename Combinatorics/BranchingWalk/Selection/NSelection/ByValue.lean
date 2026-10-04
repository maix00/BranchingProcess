/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Leftmost
public import Mathlib.Data.Prod.Lex

/-!
# Selection by a dynamic observed value

Particle labels retain identity and multiplicity, but their static order must
not be confused with spatial order.  `selectFirstNBy` orders each supplied finite
population by `(value, label)`: the observed value is primary and the label is
only a deterministic tie breaker.  Hence a new random population may be sorted
again at every generation without changing its labels.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

variable {ι Value : Type*}

/-- Dynamic spatial key: observed value first, particle identity second. -/
def valueKey [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (p : ι) : Value ×ₗ ι :=
  toLex (value p, p)

@[simp] theorem ofLex_valueKey [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (p : ι) :
    ofLex (valueKey value p) = (value p, p) :=
  rfl

theorem valueKey_injective [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) : Function.Injective (valueKey value) := by
  intro p q h
  exact congrArg (fun z : Value ×ₗ ι => (ofLex z).2) h

/-- Keep the first `N` particles after sorting by observed value and then by
their labels. -/
noncomputable def selectFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) : Finset ι := by
  classical
  exact s.filter fun p =>
    valueKey value p ∈ selectFirstN N (s.image (valueKey value))

@[simp] theorem mem_selectFirstNBy_iff [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {s : Finset ι} {p : ι} :
    p ∈ selectFirstNBy N value s ↔
      p ∈ s ∧ valueKey value p ∈ selectFirstN N (s.image (valueKey value)) := by
  classical
  simp [selectFirstNBy]

theorem selectFirstNBy_subset [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) :
    selectFirstNBy N value s ⊆ s := by
  intro p hp
  exact (mem_selectFirstNBy_iff.mp hp).1

/-- Membership in a dynamic initial segment can be tested by counting the
candidate labels with a strictly smaller dynamic key.  This formulation is
suited to measurability proofs because it avoids constructing a random sorted
list. -/
theorem mem_selectFirstNBy_iff_card_lt [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {s : Finset ι} {p : ι} :
    p ∈ selectFirstNBy N value s ↔
      p ∈ s ∧
        (s.filter fun q => valueKey value q < valueKey value p).card < N := by
  classical
  rw [mem_selectFirstNBy_iff, mem_selectFirstN_iff, rank_def]
  have himage :
      (s.image (valueKey value)).filter (fun k => k < valueKey value p) =
        (s.filter fun q => valueKey value q < valueKey value p).image
          (valueKey value) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨q, hqs, rfl⟩, hq⟩
      exact ⟨q, ⟨hqs, hq⟩, rfl⟩
    · rintro ⟨q, ⟨hqs, hq⟩, rfl⟩
      exact ⟨⟨q, hqs, rfl⟩, hq⟩
  rw [himage, Finset.card_image_of_injective _ (valueKey_injective value)]
  constructor
  · rintro ⟨hp, _, hrank⟩
    exact ⟨hp, hrank⟩
  · rintro ⟨hp, hrank⟩
    exact ⟨hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hrank⟩

/-- The finite dynamic selection is a lower set for its full dynamic key. -/
theorem mem_selectFirstNBy_of_key_lt [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} {value : ι → Value} {s : Finset ι} {p q : ι}
    (hp : p ∈ selectFirstNBy N value s) (hq : q ∈ s)
    (hqp : valueKey value q < valueKey value p) :
    q ∈ selectFirstNBy N value s := by
  rw [mem_selectFirstNBy_iff_card_lt] at hp ⊢
  refine ⟨hq, lt_of_le_of_lt ?_ hp.2⟩
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hrs, hrq⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hrs, hrq.trans hqp⟩

/-- Mapping the dynamically selected labels to their keys gives exactly the
ordinary initial segment of the key set. -/
theorem image_valueKey_selectFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) :
    (selectFirstNBy N value s).image (valueKey value) =
      selectFirstN N (s.image (valueKey value)) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact (mem_selectFirstNBy_iff.mp hp).2
  · intro hk
    have hks : k ∈ s.image (valueKey value) := selectFirstN_subset N _ hk
    obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hks
    subst k
    exact Finset.mem_image.mpr
      ⟨p, mem_selectFirstNBy_iff.mpr ⟨hp, hk⟩, rfl⟩

/-- Dynamic leftmost selection has the exact `NSelection` cardinality law. -/
theorem card_selectFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) :
    (selectFirstNBy N value s).card = min N s.card := by
  classical
  calc
    (selectFirstNBy N value s).card =
        ((selectFirstNBy N value s).image (valueKey value)).card := by
      symm
      exact Finset.card_image_of_injective _ (valueKey_injective value)
    _ = (selectFirstN N (s.image (valueKey value))).card := by
      rw [image_valueKey_selectFirstNBy]
    _ = min N (s.image (valueKey value)).card := card_selectFirstN _ _
    _ = min N s.card := by
      rw [Finset.card_image_of_injective _ (valueKey_injective value)]

/-- A lower value threshold cuts the dynamic leftmost population at the
smaller of the capacity and the candidate count below that threshold. -/
theorem card_filter_selectFirstNBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) (a : Value) :
    ((selectFirstNBy N value s).filter fun p => value p ≤ a).card =
      min N (s.filter fun p => value p ≤ a).card := by
  classical
  let key := valueKey value
  let keySet := s.image key
  let below : Value ×ₗ ι → Prop := fun k => (ofLex k).1 ≤ a
  have hselected :
      ((selectFirstNBy N value s).filter fun p => value p ≤ a).image key =
        (selectFirstN N keySet).filter below := by
    ext k
    constructor
    · intro hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hpselected, hpbelow⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨by simpa [key, keySet] using (mem_selectFirstNBy_iff.mp hpselected).2,
          by simpa [below, key] using hpbelow⟩
    · intro hk
      obtain ⟨hkselected, hkbelow⟩ := Finset.mem_filter.mp hk
      have hkset : k ∈ keySet := selectFirstN_subset N keySet hkselected
      obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hkset
      subst k
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · exact mem_selectFirstNBy_iff.mpr
          ⟨hp, by simpa [key, keySet] using hkselected⟩
      · simpa [below, key] using hkbelow
  have hdown : ∀ ⦃p q : Value ×ₗ ι⦄, p ∈ keySet → q ∈ keySet →
      q ≤ p → below p → below q := by
    intro p q _ _ hqp hp
    exact (Prod.Lex.le_iff.mp hqp).elim
      (fun hlt => le_trans (le_of_lt hlt) hp)
      (fun heq => by
        change (ofLex q).1 ≤ a
        rw [heq.1]
        exact hp)
  calc
    ((selectFirstNBy N value s).filter fun p => value p ≤ a).card =
        (((selectFirstNBy N value s).filter fun p => value p ≤ a).image key).card := by
      symm
      exact Finset.card_image_of_injective _ (valueKey_injective value)
    _ = ((selectFirstN N keySet).filter below).card := by rw [hselected]
    _ = min N (keySet.filter below).card :=
      card_filter_selectFirstN_of_downwardClosed N keySet below hdown
    _ = min N (s.filter fun p => value p ≤ a).card := by
      congr 1
      have himage : (s.filter fun p => value p ≤ a).image key =
          keySet.filter below := by
        ext k
        constructor
        · rintro hk
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩,
              by simpa [below, key] using (Finset.mem_filter.mp hp).2⟩
        · intro hk
          obtain ⟨hkset, hkbelow⟩ := Finset.mem_filter.mp hk
          obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hkset
          subst k
          exact Finset.mem_image.mpr
            ⟨p, Finset.mem_filter.mpr
              ⟨hp, by simpa [below, key] using hkbelow⟩, rfl⟩
      rw [← himage, Finset.card_image_of_injective _ (valueKey_injective value)]

/-- Dynamic-value version of the finite coupling count.  No compatibility
between a static label order and the observed values is needed. -/
theorem filter_card_le_filter_selectFirstNBy
    {κ : Type*} [DecidableEq κ] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (sourceValue : κ → Value) (targetValue : ι → Value)
    (retained source : Finset κ) (target : Finset ι)
    (hretained : retained ⊆ source)
    (hcard : retained.card ≤ N)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card) :
    ∀ a : Value,
      (retained.filter fun p => sourceValue p ≤ a).card ≤
        ((selectFirstNBy N targetValue target).filter fun q =>
          targetValue q ≤ a).card := by
  classical
  intro a
  rw [card_filter_selectFirstNBy]
  apply le_min
  · exact (Finset.card_filter_le _ _).trans hcard
  · exact (Finset.card_le_card
      (Finset.filter_subset_filter _ hretained)).trans (hthreshold a)

/-- The dynamic leftmost rule as an exact-capacity selection mechanism. -/
noncomputable def leftmostBy [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) : FiniteNSelection ι N where
  select := selectFirstNBy N value
  subset := selectFirstNBy_subset N value
  card_eq := card_selectFirstNBy N value

@[simp] theorem leftmostBy_select [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : ι → Value) (s : Finset ι) :
    (leftmostBy N value).select s = selectFirstNBy N value s :=
  rfl

/-- A particle with strictly smaller observed value has a strictly smaller
dynamic key, independently of the label tie breaker. -/
theorem valueKey_lt_of_value_lt [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) {p q : ι} (h : value p < value q) :
    valueKey value p < valueKey value q := by
  exact (Prod.Lex.lt_iff.mpr (Or.inl h))

/-- `OrderDual Value` reverses the spatial part of the dynamic key while
retaining the same particle-label tie breaker. -/
theorem valueKey_toDual_lt_iff [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (p q : ι) :
    valueKey (fun r => OrderDual.toDual (value r)) p <
        valueKey (fun r => OrderDual.toDual (value r)) q ↔
      value q < value p ∨ (value p = value q ∧ p < q) := by
  simp [valueKey, Prod.Lex.lt_iff]

end Combinatorics.Branching.Selection.NSelection

end
