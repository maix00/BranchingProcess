/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
public import Combinatorics.BranchingWalk.Selection.NSelection.ByValue
public import Mathlib.Data.Finset.Sort

/-!
# Finite-slot selection and the subadditive-array interface

This module isolates two foundations for the finite-`N` speed argument.

* `selectedSlots` applies the repository's first-`N` selector to the finite
  lexicographically labeled offspring slots `Fin N ×ₗ Fin K`;
  `measurable_selectedSlots` reuses the
  existing measurable-selection API.
* `iteratedFrontierArray` is the usual array obtained by iterating a ranked
  `N`-particle transition from the all-zero state. Its pathwise subadditivity
  follows from three deterministic one-step facts: monotonicity, translation
  covariance, and preservation of spatial order.

The finite order embedding below defines the rank reset canonically, and
Mathlib's `Finset.orderEmbOfFin` supplies its increasing enumeration. For the
bounded fixed-slot transition, input monotonicity, translation covariance,
and spatial ordering are proved. Measurability of the ranked output remains
open. The fixed-slot model gives every parent exactly `K` child slots, so it
does not represent empty or variable offspring counts and is not identified
with the general offspring point-process model.
-/

open MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching.Selection.NSelection

section FiniteSlots

variable {Ω : Type*}

/-- A finite parent/child label with its canonical lexicographic order. -/
abbrev SlotLabel (N K : ℕ) := Fin N ×ₗ Fin K

/-- Translating every spatial value by the same constant is an order
isomorphism of dynamic `(value,label)` keys. -/
def slotKeyShift {N K : ℕ} (c : ℝ) :
    (ℝ ×ₗ SlotLabel N K) ≃o (ℝ ×ₗ SlotLabel N K) :=
  Prod.Lex.prodLexCongr (OrderIso.addRight c) (OrderIso.refl _)

/-- An order isomorphism transports finite initial segments to initial
segments. This follows directly from the rank-count definition of
`selectFirstN`. -/
theorem selectFirstN_image_orderIso {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (n : ℕ) (s : Finset α) :
    (selectFirstN n s).image e = selectFirstN n (s.image e) := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [mem_selectFirstN_iff] at hx ⊢
    refine ⟨Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, ?_⟩
    have hrank : rank (s.image e) (e x) = rank s x := by
      rw [rank_def, rank_def]
      have hf : (s.image e).filter (fun z => z < e x) =
          (s.filter fun z => z < x).image e := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, haz⟩
          exact ⟨a, ⟨ha, e.lt_iff_lt.mp haz⟩, rfl⟩
        · rintro ⟨a, ⟨ha, hax⟩, rfl⟩
          exact ⟨⟨a, ha, rfl⟩, e.lt_iff_lt.mpr hax⟩
      rw [hf, Finset.card_image_of_injective _ e.injective]
    rw [hrank]
    exact hx.2
  · intro hy
    rw [mem_selectFirstN_iff] at hy
    rcases Finset.mem_image.mp hy.1 with ⟨x, hx, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨x, mem_selectFirstN_iff.mpr ⟨hx, ?_⟩, rfl⟩
    have hrank : rank (s.image e) (e x) = rank s x := by
      rw [rank_def, rank_def]
      have hf : (s.image e).filter (fun z => z < e x) =
          (s.filter fun z => z < x).image e := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, haz⟩
          exact ⟨a, ⟨ha, e.lt_iff_lt.mp haz⟩, rfl⟩
        · rintro ⟨a, ⟨ha, hax⟩, rfl⟩
          exact ⟨⟨a, ha, rfl⟩, e.lt_iff_lt.mpr hax⟩
      rw [hf, Finset.card_image_of_injective _ e.injective]
    rw [← hrank]
    exact hy.2

/-- Candidate value for a parent slot and one of its finite child slots.
This finite-slot model gives every parent exactly `K` slots; it is a bounded
special case, and does not encode zero or variable offspring counts. -/
def finiteSlotValue {N K : ℕ}
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (p : SlotLabel N K) : Ω → ℝ :=
  fun ω => position ω (ofLex p).1 + offspring ω (ofLex p).1 (ofLex p).2

/-- The finite set of the first `N` labeled offspring, selected by spatial
value and then by the canonical product order on parent/slot labels. -/
noncomputable def selectedSlots (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) : Finset (SlotLabel N K) := by
  classical
  exact selectFirstNBy N (finiteSlotValue position offspring · ω) Finset.univ

theorem selectedSlots_card (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) :
    (selectedSlots N K position offspring ω).card =
      min N (Fintype.card (SlotLabel N K)) := by
  classical
  simp [selectedSlots, card_selectFirstNBy]

/-- If there is at least one child slot, the finite selection returns exactly
`N` candidates. -/
theorem selectedSlots_card_eq (N K : ℕ) (hK : 0 < K)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) : (selectedSlots N K position offspring ω).card = N := by
  rw [selectedSlots_card]
  have hN : N ≤ Fintype.card (Fin N × Fin K) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.le_mul_of_pos_right N hK
  have hcard : Fintype.card (SlotLabel N K) = Fintype.card (Fin N × Fin K) := by
    simp [SlotLabel]
  rw [hcard]
  exact min_eq_left hN

/-- The finite set of dynamic `(value,label)` keys for all parent/child slots. -/
noncomputable def slotValueKeys (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) : Finset (ℝ ×ₗ SlotLabel N K) :=
  Finset.univ.image (valueKey (finiteSlotValue position offspring · ω))

/-- Shifting parent positions shifts every dynamic key by the same ordered
key translation. -/
theorem slotValueKeys_shift (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (c : ℝ) :
    slotValueKeys N K (fun ξ i => position ξ i + c) offspring ω =
      (slotValueKeys N K position offspring ω).image (slotKeyShift c) := by
  classical
  rw [slotValueKeys, slotValueKeys, Finset.image_image]
  congr 1
  funext p
  simp [slotKeyShift, finiteSlotValue, valueKey]
  ring

/-- When there are at least `N` finite child slots, the initial segment of
dynamic keys has cardinality exactly `N`. -/
theorem slotValueKeys_selected_card (N K : ℕ) (hK : 0 < K)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) :
    (selectFirstN N (slotValueKeys N K position offspring ω)).card = N := by
  classical
  rw [slotValueKeys, card_selectFirstN]
  rw [Finset.card_image_of_injective _ (valueKey_injective _)]
  simp only [Finset.card_univ]
  have hcard : Fintype.card (SlotLabel N K) = N * K := by
    simp [SlotLabel]
  rw [hcard]
  exact min_eq_left (Nat.le_mul_of_pos_right N hK)

/-- The spatial rank order on the selected labeled slots. The value key uses
the label only to break ties, so every selected candidate has a unique rank. -/
noncomputable def selectedSlotRank (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) : Fin N ↪o (ℝ ×ₗ SlotLabel N K) := by
  classical
  exact (selectFirstN N (slotValueKeys N K position offspring ω)).orderEmbOfFin
    (slotValueKeys_selected_card N K hK position offspring ω)

/-- Every rank in `selectedSlotRank` is in the selected first-`N` key set. -/
theorem selectedSlotRank_mem (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (i : Fin N) :
    selectedSlotRank N K position offspring ω hK i ∈
      selectFirstN N
        (Finset.univ.image
          (valueKey (finiteSlotValue position offspring · ω))) := by
  classical
  change (selectFirstN N (slotValueKeys N K position offspring ω)).orderEmbOfFin
      (slotValueKeys_selected_card N K hK position offspring ω) i ∈
    selectFirstN N (slotValueKeys N K position offspring ω)
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Spatial rank is strictly increasing in the full `(value,label)` order. -/
theorem selectedSlotRank_strictMono (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) :
    StrictMono (selectedSlotRank N K position offspring ω hK) :=
  (selectedSlotRank N K position offspring ω hK).strictMono

/-- Shifting every parent position translates each selected rank by the same
ordered-key isomorphism. In particular, selection and spatial rank reset
commute with a common spatial translation. -/
theorem selectedSlotRank_shift (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (c : ℝ) :
    selectedSlotRank N K (fun ξ i => position ξ i + c) offspring ω hK =
      (selectedSlotRank N K position offspring ω hK).comp
        (slotKeyShift c).toOrderEmbedding := by
  classical
  change (selectFirstN N
      (slotValueKeys N K (fun ξ i => position ξ i + c) offspring ω)).orderEmbOfFin
        (slotValueKeys_selected_card N K hK (fun ξ i => position ξ i + c)
          offspring ω) =
    ((selectFirstN N (slotValueKeys N K position offspring ω)).orderEmbOfFin
      (slotValueKeys_selected_card N K hK position offspring ω)).comp
        (slotKeyShift c).toOrderEmbedding
  symm
  apply Finset.orderEmbOfFin_unique'
    (s := selectFirstN N
      (slotValueKeys N K (fun ξ i => position ξ i + c) offspring ω))
    (h := slotValueKeys_selected_card N K hK
      (fun ξ i => position ξ i + c) offspring ω)
    (f := (selectFirstN N (slotValueKeys N K position offspring ω)).orderEmbOfFin
      (slotValueKeys_selected_card N K hK position offspring ω) |>.comp
        (slotKeyShift c).toOrderEmbedding)
  intro i
  have hfirst :
      (selectFirstN N (slotValueKeys N K position offspring ω)).image
          (slotKeyShift c) =
        selectFirstN N (slotValueKeys N K (fun ξ i => position ξ i + c)
          offspring ω) := by
    rw [slotValueKeys_shift]
    exact selectFirstN_image_orderIso (slotKeyShift c) N
      (slotValueKeys N K position offspring ω)
  change slotKeyShift c
      (selectedSlotRank N K position offspring ω hK i) ∈
    selectFirstN N (slotValueKeys N K (fun ξ i => position ξ i + c)
      offspring ω)
  rw [← hfirst]
  exact Finset.mem_image.mpr
    ⟨selectedSlotRank N K position offspring ω hK i,
      selectedSlotRank_mem N K position offspring ω hK i, rfl⟩

/-- Value at a selected spatial rank. The full key order breaks equal-value
ties by parent/slot label, while this projection records the spatial value. -/
noncomputable def selectedSlotPosition (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (i : Fin N) : ℝ :=
  (ofLex (selectedSlotRank N K position offspring ω hK i)).1

/-- The ranked spatial values commute with common translation. -/
theorem selectedSlotPosition_shift (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (c : ℝ) (i : Fin N) :
    selectedSlotPosition N K (fun ξ i => position ξ i + c) offspring ω hK i =
      selectedSlotPosition N K position offspring ω hK i + c := by
  rw [selectedSlotPosition, selectedSlotPosition,
    selectedSlotRank_shift N K position offspring ω hK c]
  simp [slotKeyShift]

/-- The rank reset returns values in nondecreasing spatial order. -/
theorem selectedSlotPosition_monotone (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) :
    Monotone (selectedSlotPosition N K position offspring ω hK) := by
  exact Prod.Lex.monotone_fst_ofLex.comp
    (selectedSlotRank N K position offspring ω hK).monotone

/-- For a nondecreasing finite sequence, the `i`th term lies below a
threshold whenever the threshold captures more than `i` terms. -/
theorem monotone_fin_le_of_filter_card_gt {N : ℕ} (f : Fin N → ℝ)
    (hf : Monotone f) (i : Fin N) (a : ℝ)
    (hcount : (Finset.univ.filter fun j : Fin N => f j ≤ a).card > i.val) :
    f i ≤ a := by
  by_contra hia
  have hia' : a < f i := lt_of_not_ge hia
  have hsub : (Finset.univ.filter fun j : Fin N => f j ≤ a) ⊆ Finset.Iio i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Iio]
    by_contra hji
    have hij : i ≤ j := le_of_not_gt hji
    exact (not_lt_of_ge ((hf hij).trans hj.2)) hia'
  have hcard := Finset.card_le_card hsub
  have hcard' : (Finset.univ.filter fun j : Fin N => f j ≤ a).card ≤ i.val := by
    simpa using hcard
  omega

/-- The first `i+1` terms of a nondecreasing finite sequence all lie below
the value at index `i`. -/
theorem monotone_fin_filter_card_gt_of_le {N : ℕ} (f : Fin N → ℝ)
    (hf : Monotone f) (i : Fin N) (a : ℝ) (hia : f i ≤ a) :
    (Finset.univ.filter fun j : Fin N => f j ≤ a).card > i.val := by
  have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j : Fin N => f j ≤ a := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (hf (Finset.mem_Iic.mp hj)).trans hia
  have hcard := Finset.card_le_card hsub
  have hiic : (Finset.Iic i : Finset (Fin N)).card = i.val + 1 := by simp
  omega

/-- The selected rank enumeration has the same threshold counts as the
underlying selected labels. -/
theorem selectedSlotPosition_filter_card (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (a : ℝ) :
    (Finset.univ.filter fun i : Fin N =>
      selectedSlotPosition N K position offspring ω hK i ≤ a).card =
    ((selectedSlots N K position offspring ω).filter fun p =>
      finiteSlotValue position offspring p ω ≤ a).card := by
  classical
  let rank := selectedSlotRank N K position offspring ω hK
  let key := valueKey (finiteSlotValue position offspring · ω)
  let selectedKey := selectFirstN N (slotValueKeys N K position offspring ω)
  have hrankImage : Finset.univ.image rank = selectedKey := by
    simpa [rank, selectedKey, selectedSlotRank, slotValueKeys] using
      (Finset.image_orderEmbOfFin_univ
        (selectFirstN N (slotValueKeys N K position offspring ω))
        (slotValueKeys_selected_card N K hK position offspring ω))
  have hslotImage : (selectedSlots N K position offspring ω).image key =
      selectedKey := by
    simpa [key, selectedKey, selectedSlots, slotValueKeys] using
      image_valueKey_selectFirstNBy N
        (finiteSlotValue position offspring · ω) Finset.univ
  have hrankFilter :
      (Finset.univ.filter fun i : Fin N => (ofLex (rank i)).1 ≤ a).image rank =
        selectedKey.filter fun q => (ofLex q).1 ≤ a := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [← hrankImage]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mp hi |>.1, rfl⟩
      · exact (Finset.mem_filter.mp hi).2
    · intro hq
      obtain ⟨hqkey, hqvalue⟩ := Finset.mem_filter.mp hq
      rw [← hrankImage] at hqkey
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hqkey
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact hqvalue
  have hslotFilter :
      ((selectedSlots N K position offspring ω).filter fun p =>
        finiteSlotValue position offspring p ω ≤ a).image key =
          selectedKey.filter fun q => (ofLex q).1 ≤ a := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [← hslotImage]
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mp hp |>.1, rfl⟩
      · simpa [key, valueKey] using (Finset.mem_filter.mp hp).2
    · intro hq
      obtain ⟨hqkey, hqvalue⟩ := Finset.mem_filter.mp hq
      rw [← hslotImage] at hqkey
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqkey
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
      simpa [key, valueKey] using hqvalue
  calc
    (Finset.univ.filter fun i : Fin N => (ofLex (rank i)).1 ≤ a).card =
        ((Finset.univ.filter fun i : Fin N => (ofLex (rank i)).1 ≤ a).image rank).card := by
          symm
          exact Finset.card_image_of_injective _ rank.injective
    _ = (selectedKey.filter fun q => (ofLex q).1 ≤ a).card := by rw [hrankFilter]
    _ = (((selectedSlots N K position offspring ω).filter fun p =>
        finiteSlotValue position offspring p ω ≤ a).image key).card := by rw [hslotFilter]
    _ = ((selectedSlots N K position offspring ω).filter fun p =>
        finiteSlotValue position offspring p ω ≤ a).card := by
          exact Finset.card_image_of_injective _
            (valueKey_injective (finiteSlotValue position offspring · ω))

/-- A ranked key is exactly the key of a label retained by `selectedSlots`.
Thus the sorted key enumeration and the existing measurable label selector
describe the same finite population. -/
theorem selectedSlotRank_label_mem (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (i : Fin N) :
    ∃ p : SlotLabel N K,
      valueKey (finiteSlotValue position offspring · ω) p =
          selectedSlotRank N K position offspring ω hK i ∧
        p ∈ selectedSlots N K position offspring ω := by
  have hmem : selectedSlotRank N K position offspring ω hK i ∈
      slotValueKeys N K position offspring ω := by
    rw [slotValueKeys]
    exact selectFirstN_subset N _ (selectedSlotRank_mem N K position offspring ω hK i)
  rcases Finset.mem_image.mp hmem with ⟨p, -, hp⟩
  refine ⟨p, hp, ?_⟩
  change p ∈ selectFirstNBy N (finiteSlotValue position offspring · ω) Finset.univ
  rw [mem_selectFirstNBy_iff]
  refine ⟨Finset.mem_univ p, ?_⟩
  rw [hp]
  exact selectedSlotRank_mem N K position offspring ω hK i

/-- Each rank in the finite reset is the value of an actual parent/child slot.
The fixed-`K` model used here assumes every parent has exactly `K` slots, so it
does not represent empty or variable offspring populations. -/
theorem selectedSlotPosition_isCandidate (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (ω : Ω) (hK : 0 < K) (i : Fin N) :
    ∃ p : SlotLabel N K,
      selectedSlotPosition N K position offspring ω hK i = finiteSlotValue position offspring p ω := by
  rcases selectedSlotRank_label_mem N K position offspring ω hK i with
    ⟨p, hp, _⟩
  refine ⟨p, ?_⟩
  change (ofLex (selectedSlotRank N K position offspring ω hK i)).1 = _
  rw [← hp]
  rfl

/-- The concrete finite-slot one-step transition: form all `N * K` child
positions, keep the first `N` by spatial value, and reset their indices to
spatial rank. It is defined only when `K > 0`, so the output has `N` entries. -/
noncomputable def finiteSlotSelectionStep (N K : ℕ)
    (offspring : Ω → Fin N → Fin K → ℝ) (ω : Ω) (hK : 0 < K)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  selectedSlotPosition N K (fun _ i => x i) offspring ω hK

/-- In the fixed-`K` finite-slot model, the selection step is monotone in a
spatially ranked input configuration. Pointwise input domination induces
domination of every candidate; the existing threshold-count formula for
first-`N` selection then compares the ordered output coordinates. This lemma
does not assert a result for variable-size offspring populations. -/
theorem finiteSlotSelectionStep_monotone (N K : ℕ)
    (offspring : Ω → Fin N → Fin K → ℝ) (ω : Ω) (hK : 0 < K)
    {x y : Fin N → ℝ} (hxy : ∀ i, x i ≤ y i) :
    ∀ i, finiteSlotSelectionStep N K offspring ω hK x i ≤
      finiteSlotSelectionStep N K offspring ω hK y i := by
  intro i
  let a := finiteSlotSelectionStep N K offspring ω hK y i
  let vx : SlotLabel N K → ℝ := fun p =>
    finiteSlotValue (fun _ j => x j) offspring p ω
  let vy : SlotLabel N K → ℝ := fun p =>
    finiteSlotValue (fun _ j => y j) offspring p ω
  have hxyCandidate : ∀ p, vx p ≤ vy p := by
    intro p
    dsimp [vx, vy, finiteSlotValue]
    exact add_le_add (hxy (ofLex p).1) le_rfl
  have hfiltered :
      (Finset.univ.filter fun p : SlotLabel N K => vy p ≤ a) ⊆
        Finset.univ.filter fun p : SlotLabel N K => vx p ≤ a := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, (hxyCandidate p).trans hp.2⟩
  have hcountsAll := Finset.card_le_card hfiltered
  have hselectedX :
      ((selectedSlots N K (fun _ j => x j) offspring ω).filter fun p => vx p ≤ a).card =
        min N (Finset.univ.filter fun p : SlotLabel N K => vx p ≤ a).card := by
    simpa [selectedSlots, vx] using
      card_filter_selectFirstNBy N vx Finset.univ a
  have hselectedY :
      ((selectedSlots N K (fun _ j => y j) offspring ω).filter fun p => vy p ≤ a).card =
        min N (Finset.univ.filter fun p : SlotLabel N K => vy p ≤ a).card := by
    simpa [selectedSlots, vy] using
      card_filter_selectFirstNBy N vy Finset.univ a
  have hpositionX := selectedSlotPosition_filter_card N K
    (fun _ j => x j) offspring ω hK a
  have hpositionY := selectedSlotPosition_filter_card N K
    (fun _ j => y j) offspring ω hK a
  have hpositionCount :
      (Finset.univ.filter fun j : Fin N =>
        finiteSlotSelectionStep N K offspring ω hK x j ≤ a).card ≥
      (Finset.univ.filter fun j : Fin N =>
        finiteSlotSelectionStep N K offspring ω hK y j ≤ a).card := by
    change (Finset.univ.filter fun j : Fin N =>
        selectedSlotPosition N K (fun _ j => x j) offspring ω hK j ≤ a).card ≥
      (Finset.univ.filter fun j : Fin N =>
        selectedSlotPosition N K (fun _ j => y j) offspring ω hK j ≤ a).card
    rw [hpositionX, hpositionY, hselectedX, hselectedY]
    exact min_le_min_left N hcountsAll
  have hycount :
      (Finset.univ.filter fun j : Fin N =>
        finiteSlotSelectionStep N K offspring ω hK y j ≤ a).card > i.val := by
    apply monotone_fin_filter_card_gt_of_le
      (finiteSlotSelectionStep N K offspring ω hK y)
      (selectedSlotPosition_monotone N K (fun _ j => y j) offspring ω hK) i a
    exact le_of_eq (by simp [a])
  have hxcount :
      (Finset.univ.filter fun j : Fin N =>
        finiteSlotSelectionStep N K offspring ω hK x j ≤ a).card > i.val := by
    omega
  exact monotone_fin_le_of_filter_card_gt
    (finiteSlotSelectionStep N K offspring ω hK x)
    (selectedSlotPosition_monotone N K (fun _ j => x j) offspring ω hK) i a hxcount

/-- The concrete finite-slot transition returns a nondecreasing ranked vector. -/
theorem finiteSlotSelectionStep_sorted (N K : ℕ)
    (offspring : Ω → Fin N → Fin K → ℝ) (ω : Ω) (hK : 0 < K)
    (x : Fin N → ℝ) :
    Monotone (finiteSlotSelectionStep N K offspring ω hK x) :=
  selectedSlotPosition_monotone N K (fun _ i => x i) offspring ω hK

/-- The finite-slot transition commutes with common translations. -/
theorem finiteSlotSelectionStep_shift (N K : ℕ)
    (offspring : Ω → Fin N → Fin K → ℝ) (ω : Ω) (hK : 0 < K)
    (x : Fin N → ℝ) (c : ℝ) :
    finiteSlotSelectionStep N K offspring ω hK (fun i => x i + c) =
      fun i => finiteSlotSelectionStep N K offspring ω hK x i + c := by
  funext i
  exact selectedSlotPosition_shift N K (fun _ j => x j) offspring ω hK c i

/-- When `N > 0`, the first coordinate of the finite-slot reset is a minimum. -/
theorem finiteSlotSelectionStep_minimum (N K : ℕ) (hN : 0 < N)
    (offspring : Ω → Fin N → Fin K → ℝ) (ω : Ω) (hK : 0 < K)
    (x : Fin N → ℝ) :
    ∀ i, finiteSlotSelectionStep N K offspring ω hK x ⟨0, hN⟩ ≤
      finiteSlotSelectionStep N K offspring ω hK x i := by
  intro i
  apply finiteSlotSelectionStep_sorted N K offspring ω hK x
  apply Fin.le_iff_val_le_val.mpr
  exact Nat.zero_le i.val

/-- Measurability of the one-step selected labels. This uses the existing
finite dynamic selector directly; no measurable sorting or rank operation is
claimed here. -/
theorem measurable_selectedSlots [MeasurableSpace Ω] (N K : ℕ)
    (position : Ω → Fin N → ℝ) (offspring : Ω → Fin N → Fin K → ℝ)
    (hposition : ∀ i, Measurable fun ω => position ω i)
    (hoffspring : ∀ i j, Measurable fun ω => offspring ω i j) :
    Measurable (selectedSlots N K position offspring) := by
  classical
  change Measurable fun ω =>
    selectFirstNBy N (finiteSlotValue position offspring · ω) Finset.univ
  exact NSelection.measurable_selectFirstNBy_fixed N
    (fun ω p => finiteSlotValue position offspring p ω) Finset.univ (by
      intro p q
      exact NSelection.measurable_valueKey_lt
        (fun ω r => finiteSlotValue position offspring r ω)
        (fun r => (hposition (ofLex r).1).add
          (hoffspring (ofLex r).1 (ofLex r).2)) p q)

end FiniteSlots

section RankedArray

variable {N Ω : Type*} [Fintype N] [Nonempty N] [MeasurableSpace Ω]

/-- A configuration of `N` ranked particles on the real line. -/
abbrev Configuration (N : Type*) := N → ℝ

/-- Translation of a ranked particle configuration. -/
def translateConfiguration {N : Type*} (x : Configuration N) (c : ℝ) :
    Configuration N := fun i => x i + c

/-- A configuration is in spatial order when its distinguished first particle
is a minimum. -/
def SpatiallyOrdered {N : Type*} [Nonempty N] (x : Configuration N)
    (first : N) : Prop :=
  ∀ i, x first ≤ x i

/-- Iterate a time-dependent ranked one-step transition. -/
def iterateTransition {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (x : Configuration N) : Configuration N :=
  match length with
  | 0 => x
  | k + 1 => step (start + k) ω (iterateTransition step start k ω x)

theorem iterateTransition_add
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (start k l : ℕ) (ω : Ω) (x : Configuration N) :
    iterateTransition step start (k + l) ω x =
      iterateTransition step (start + k) l ω
        (iterateTransition step start k ω x) := by
  induction l with
  | zero => simp [iterateTransition]
  | succ l ih =>
      rw [Nat.add_succ, iterateTransition, iterateTransition, ih]
      congr 1
      omega

theorem iterateTransition_monotone
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t ω x y, (∀ i, x i ≤ y i) → ∀ i, step t ω x i ≤ step t ω y i)
    (start length : ℕ) (ω : Ω) {x y : Configuration N}
    (hxy : ∀ i, x i ≤ y i) :
    ∀ i, iterateTransition step start length ω x i ≤
      iterateTransition step start length ω y i := by
  induction length generalizing start x y with
  | zero => exact hxy
  | succ n ih =>
      intro i
      simp only [iterateTransition]
      apply hstep
      exact ih (start := start) hxy

theorem iterateTransition_translate
    {N Ω : Type*} (step : ℕ → Ω → Configuration N → Configuration N)
    (hshift : ∀ t ω x c,
      step t ω (translateConfiguration x c) =
        translateConfiguration (step t ω x) c)
    (start length : ℕ) (ω : Ω) (x : Configuration N) (c : ℝ) :
    iterateTransition step start length ω (translateConfiguration x c) =
      translateConfiguration (iterateTransition step start length ω x) c := by
  induction length generalizing start x with
  | zero => rfl
  | succ n ih =>
      simp only [iterateTransition]
      rw [ih, hshift]

theorem iterateTransition_spatiallyOrdered
    {N Ω : Type*} [Nonempty N]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (first : N)
    (hordered : ∀ t ω x, SpatiallyOrdered (step t ω x) first)
    (start length : ℕ) (ω : Ω) (x : Configuration N)
    (hx : SpatiallyOrdered x first) :
    SpatiallyOrdered (iterateTransition step start length ω x) first := by
  induction length generalizing start x with
  | zero => exact hx
  | succ n _ =>
      rw [iterateTransition]
      exact hordered (start + n) ω
        (iterateTransition step start n ω x)

/-- The first particle position in the population obtained by restarting the
ranked finite-`N` transition at `start` for `length` generations, from the
all-zero configuration. -/
def iteratedFrontier {N Ω : Type*} [Fintype N] [Nonempty N]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (first : N) : ℝ :=
  iterateTransition step start length ω (fun _ => 0) first

/-- Negative minimum displacement of a ranked `N`-selection block. -/
def iteratedFrontierArray {N Ω : Type*} [Fintype N] [Nonempty N]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (start length : ℕ) (ω : Ω) (first : N) : ℝ :=
  -iteratedFrontier step start length ω first

/-- The finite-`N` block array is pathwise subadditive whenever the concrete
one-step transition is monotone in every input coordinate, commutes with
translations, and returns the configuration in spatial order. This is the
deterministic core of the restart comparison; an actual selection kernel must
still discharge these three hypotheses. -/
theorem iteratedFrontierArray_subadditive
    {N Ω : Type*} [Fintype N] [Nonempty N]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (first : N)
    (hstepMono : ∀ t ω x y, (∀ i, x i ≤ y i) →
      ∀ i, step t ω x i ≤ step t ω y i)
    (hstepShift : ∀ t ω x c,
      step t ω (translateConfiguration x c) =
        translateConfiguration (step t ω x) c)
    (hstepOrdered : ∀ t ω x, SpatiallyOrdered (step t ω x) first) :
    ∀ start k l ω,
      iteratedFrontierArray step start (k + l) ω first ≤
        iteratedFrontierArray step start k ω first +
          iteratedFrontierArray step (start + k) l ω first := by
  intro start k l ω
  have hordered : ∀ m, SpatiallyOrdered
      (iterateTransition step m k ω (fun _ => 0)) first := by
    intro m
    exact iterateTransition_spatiallyOrdered step first hstepOrdered m k ω
      (fun _ => 0) (fun i => by simp)
  have hfront : ∀ i,
      iterateTransition step start k ω (fun _ => 0) first ≤
        iterateTransition step start k ω (fun _ => 0) i :=
    (hordered start)
  have hconst : ∀ i,
      (fun _ : N => iterateTransition step start k ω (fun _ => 0) first) i ≤
        iterateTransition step start k ω (fun _ => 0) i := by
    intro i
    exact hfront i
  have hfuture := iterateTransition_monotone step hstepMono
    (start + k) l ω hconst
  have hshift := iterateTransition_translate step hstepShift
    (start + k) l ω (fun _ : N => 0)
    (iterateTransition step start k ω (fun _ => 0) first)
  have hcomp := iterateTransition_add step start k l ω (fun _ => 0)
  have hcoord :
      iteratedFrontier step start (k + l) ω first ≥
        iteratedFrontier step start k ω first +
          iteratedFrontier step (start + k) l ω first := by
    change iterateTransition step start (k + l) ω (fun _ => 0) first ≥ _
    rw [hcomp]
    have hfutureFirst := hfuture first
    have hconst_eq :
        (fun _ : N => iterateTransition step start k ω (fun _ => 0) first) =
          translateConfiguration (fun _ => 0)
            (iterateTransition step start k ω (fun _ => 0) first) := by
      funext i
      simp [translateConfiguration]
    rw [hconst_eq, hshift] at hfutureFirst
    have hfutureFirst' :
        iteratedFrontier step start k ω first +
          iteratedFrontier step (start + k) l ω first ≤
        iterateTransition step (start + k) l ω
          (iterateTransition step start k ω (fun _ => 0)) first := by
      simpa [iteratedFrontier, translateConfiguration, add_comm] using hfutureFirst
    exact hfutureFirst'
  unfold iteratedFrontierArray
  linarith

/-- Joint measurability of iterated transitions follows by induction from a
jointly measurable one-step map. -/
theorem measurable_iterateTransition
    {N Ω : Type*} [Fintype N] [MeasurableSpace Ω]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t, Measurable fun p : Ω × Configuration N => step t p.1 p.2)
    (start length : ℕ) (initial : Ω → Configuration N) (hinitial : Measurable initial) :
    Measurable fun ω => iterateTransition step start length ω (initial ω) := by
  induction length generalizing start initial with
  | zero => simpa [iterateTransition] using hinitial
  | succ n ih =>
      simp only [iterateTransition]
      exact (hstep (start + n)).comp (measurable_id.prodMk
        (ih (start := start) initial hinitial))

/-- Measurability of the finite-`N` block array is a direct consequence of
measurability of the ranked transition. -/
theorem measurable_iteratedFrontierArray
    {N Ω : Type*} [Fintype N] [Nonempty N] [MeasurableSpace Ω]
    (step : ℕ → Ω → Configuration N → Configuration N)
    (hstep : ∀ t, Measurable fun p : Ω × Configuration N => step t p.1 p.2)
    (start length : ℕ) (first : N) :
    Measurable fun ω => iteratedFrontierArray step start length ω first := by
  unfold iteratedFrontierArray iteratedFrontier
  exact measurable_neg.comp <| (measurable_pi_apply first).comp <|
    measurable_iterateTransition step hstep start length (fun _ _ => 0)
      measurable_const

end RankedArray

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
