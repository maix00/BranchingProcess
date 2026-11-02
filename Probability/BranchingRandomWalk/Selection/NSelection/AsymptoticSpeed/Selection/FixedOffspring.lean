/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.NSelection.ByValue
public import Combinatorics.Selection.NSelection.Mechanism.Finite.ByValue
public import Mathlib.Data.Finset.Sort

/-!
# Fixed finite-slot selection

For each of \(N\) parents, this model assigns exactly \(K\) child displacements
and selects the first \(N\) candidate positions under the value-and-label order.
Writing \(v(i,j)=x_i+z_{i,j}\) for the candidate values, `selectedSlots`
returns the retained labels, `slotValueKeys` their value-and-label keys,
`selectedSlotRank` the increasing rank enumeration, and
`selectedSlotPosition` the spatial value at each rank. This fixed-\(K\) model
does not encode zero or variable offspring counts.

## Public declarations

The declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed` are:

- `SlotLabel` defines lexicographically ordered parent-slot labels;
  `slotKeyShift` translates all spatial key values by \(c\);
  `finiteSlotValue` defines \(v(i,j)=x_i+z_{i,j}\); and `selectedSlots`
  selects the first \(N\) labels.
- `selectedSlots_card` states
  \(\#\operatorname{selectedSlots}=\min(N,NK)\);
  `selectedSlots_card_eq` gives cardinality \(N\) when \(K>0\).
- `slotValueKeys` defines the key set \(\mathcal K_x\).
  `slotValueKeys_shift` gives
  \(\mathcal K_{x+c}=(\mathcal K_x).image(\texttt{slotKeyShift}(c))\),
  and `slotValueKeys_selected_card` states that the first-\(N\) key set has
  cardinality \(N\) when \(K>0\).
- `selectedSlotRank` defines the order embedding \(r_x\) from `Fin N` into the
  selected keys; `selectedSlotRank_mem` gives membership,
  `selectedSlotRank_strictMono` states \(i<j\) implies \(r_x(i)<r_x(j)\), and
  `selectedSlotRank_shift` gives
  \(r_{x+c}=\texttt{slotKeyShift}(c)\circ r_x\).
- `selectedSlotPosition` defines \(p_x(i)=\operatorname{value}(r_x(i))\).
  `selectedSlotPosition_shift` gives \(p_{x+c}(i)=p_x(i)+c\),
  `selectedSlotPosition_monotone` states \(i\le j\) implies
  \(p_x(i)\le p_x(j)\), and `selectedSlotPosition_filter_card` gives
  \(\#\{i:p_x(i)\le a\}=\#\{q\in\operatorname{selectedSlots}:v(q)\le a\}\).
  `selectedSlotRank_label_mem` identifies each rank with a selected label,
  and `selectedSlotPosition_isCandidate` states each ranked position is a
  candidate value.
- `finiteSlotSelectionStep` defines the one-generation ranked transition
  \(F\). `finiteSlotSelectionStep_monotone` states \(x\le y\) implies
  \(F(x)\le F(y)\) coordinatewise; `finiteSlotSelectionStep_sorted` gives
  \(i\le j\) implies \(F(x)_i\le F(x)_j\);
  `finiteSlotSelectionStep_shift` gives \(F(x+c)=F(x)+c\); and
  `finiteSlotSelectionStep_minimum` gives \(F(x)_0\le F(x)_i\) when \(N>0\).
- `measurable_selectedSlots` states measurability of the selected set when
  every parent position and child displacement is measurable.

`Finset.orderEmbOfFin` from Mathlib's `Mathlib/Data/Finset/Sort` supplies the
finite increasing enumeration used by `selectedSlotRank`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open _root_.Combinatorics.Selection.NSelection

section FiniteSlots

variable {Ω : Type*}

/-- A finite parent/child label with its canonical lexicographic order. -/
abbrev SlotLabel (N K : ℕ) := Fin N ×ₗ Fin K

/-- Translating every spatial value by the same constant is an order
isomorphism of dynamic `(value,label)` keys. -/
def slotKeyShift {N K : ℕ} (c : ℝ) :
    (ℝ ×ₗ SlotLabel N K) ≃o (ℝ ×ₗ SlotLabel N K) :=
  Prod.Lex.prodLexCongr (OrderIso.addRight c) (OrderIso.refl _)

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
private lemma monotone_fin_le_of_filter_card_gt {N : ℕ} (f : Fin N → ℝ)
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
private lemma monotone_fin_filter_card_gt_of_le {N : ℕ} (f : Fin N → ℝ)
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
    simp [rank, selectedKey, selectedSlotRank, slotValueKeys]
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
  exact Combinatorics.Selection.NSelection.measurable_selectFirstNBy_fixed N
    (fun ω p => finiteSlotValue position offspring p ω) Finset.univ (by
      intro p q
      exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
        (fun ω r => finiteSlotValue position offspring r ω)
        (fun r => (hposition (ofLex r).1).add
          (hoffspring (ofLex r).1 (ofLex r).2)) p q)

end FiniteSlots


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
