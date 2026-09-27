import Combinatorics.BranchingWalk.Selection.NSelection.Leftmost

/-!
# The rightmost selection mechanism is the order dual of the leftmost one

Reversing the order of the line turns "the `N` leftmost candidates" into "the
`N` rightmost candidates". This module records that as an equality of selection
mechanisms: `selectLastN` is `selectFirstN` after applying `OrderDual`, and
`rightmost` is the `OrderDual` transport of `leftmost`. Consequently the
right-hand version of every selection statement is an instance of the
left-hand one rather than a second theory.

The transport of a mechanism along `OrderDual` is `NSelection.mapOrderDual`.
Since a mechanism is a deterministic object, the same construction applies to
every mechanism, not only to the leftmost one.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

namespace NSelection

variable {ι : Type*}

/-! ### The two orders of the line -/

theorem isLeast_image_toDual_iff [LE ι] {s : Set ι} {x : ι} :
    IsLeast (OrderDual.toDual '' s) (OrderDual.toDual x) ↔ IsGreatest s x := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro y hy
      exact (OrderDual.toDual_le_toDual).1 (hmin ⟨y, hy, rfl⟩)
  · rintro ⟨hx, hmax⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (OrderDual.toDual_le_toDual).2 (hmax hy)

theorem isGreatest_image_ofDual_iff [LE ι] {s : Set (OrderDual ι)} {x : ι} :
    IsGreatest (OrderDual.ofDual '' s) x ↔ IsLeast s (OrderDual.toDual x) := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro z hz
      have h := hmax ⟨z, hz, rfl⟩
      simpa using (OrderDual.toDual_le_toDual (a := x) (b := OrderDual.ofDual z)).2 h
  · rintro ⟨hx, hmin⟩
    refine ⟨⟨OrderDual.toDual x, by simpa using hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h := hmin hz
    simpa using (OrderDual.toDual_le_toDual (a := x) (b := OrderDual.ofDual z)).1 h

/-- The companion of `isLeast_image_toDual_iff`: the reversed set has
`toDual x` as a greatest element exactly when `x` is least in the original
set. -/
theorem isGreatest_image_toDual_iff [LE ι] {s : Set ι} {x : ι} :
    IsGreatest (OrderDual.toDual '' s) (OrderDual.toDual x) ↔ IsLeast s x := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro y hy
      exact (OrderDual.toDual_le_toDual).1 (hmax ⟨y, hy, rfl⟩)
  · rintro ⟨hx, hmin⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (OrderDual.toDual_le_toDual).2 (hmin hy)

/-! ### The dual reading of the selection rules -/

section Mirror

variable [LinearOrder ι] [DecidableEq ι]

omit [LinearOrder ι] in
theorem toDual_mem_image_toDual_iff {s : Finset ι} {q : ι} :
    OrderDual.toDual q ∈ s.image OrderDual.toDual ↔ q ∈ s := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, haq⟩
    obtain rfl := OrderDual.toDual_inj.mp haq
    exact ha
  · intro hq
    exact ⟨q, hq, rfl⟩

theorem rank_image_toDual (s : Finset ι) (q : ι) :
    rank (s.image OrderDual.toDual) (OrderDual.toDual q) =
      (s.filter fun p => q < p).card := by
  have h : (s.image OrderDual.toDual).filter (fun p => p < OrderDual.toDual q)
      = (s.filter fun p => q < p).image OrderDual.toDual := by
    rw [Finset.filter_image]
    rw [show s.filter (fun a => OrderDual.toDual a < OrderDual.toDual q)
        = s.filter (fun p => q < p) from
      Finset.filter_congr fun p _ => OrderDual.toDual_lt_toDual]
  rw [rank, h]
  exact Finset.card_image_of_injective _ OrderDual.toDual.injective

theorem reverseRank_image_toDual (s : Finset ι) (q : ι) :
    ((s.image OrderDual.toDual).filter fun p => OrderDual.toDual q < p).card =
      (s.filter fun p => p < q).card := by
  have h : (s.image OrderDual.toDual).filter (fun p => OrderDual.toDual q < p)
      = (s.filter fun p => p < q).image OrderDual.toDual := by
    rw [Finset.filter_image]
    rw [show s.filter (fun a => OrderDual.toDual q < OrderDual.toDual a)
        = s.filter (fun p => p < q) from
      Finset.filter_congr fun p _ => OrderDual.toDual_lt_toDual]
  rw [h]
  exact Finset.card_image_of_injective _ OrderDual.toDual.injective

/-- The leftmost rule on the reversed order is the rightmost rule on the
original order. -/
theorem mem_selectFirstN_image_toDual_iff {N : ℕ} {s : Finset ι} {q : ι} :
    OrderDual.toDual q ∈ selectFirstN N (s.image OrderDual.toDual) ↔ q ∈ selectLastN N s := by
  rw [mem_selectFirstN_iff, mem_selectLastN_iff, rank_image_toDual]
  constructor
  · rintro ⟨hq, h⟩
    exact ⟨toDual_mem_image_toDual_iff.mp hq, h⟩
  · rintro ⟨hq, h⟩
    exact ⟨toDual_mem_image_toDual_iff.mpr hq, h⟩

theorem mem_selectLastN_image_toDual_iff {N : ℕ} {s : Finset ι} {q : ι} :
    OrderDual.toDual q ∈ selectLastN N (s.image OrderDual.toDual) ↔ q ∈ selectFirstN N s := by
  rw [mem_selectLastN_iff, mem_selectFirstN_iff, toDual_mem_image_toDual_iff,
    reverseRank_image_toDual, rank]

theorem selectFirstN_image_toDual (N : ℕ) (s : Finset ι) :
    selectFirstN N (s.image OrderDual.toDual) = (selectLastN N s).image OrderDual.toDual := by
  ext q
  rw [Finset.mem_image]
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp
      (selectFirstN_subset N (s.image OrderDual.toDual) hq)
    refine ⟨p, ?_, hpq⟩
    rw [← hpq] at hq
    exact mem_selectFirstN_image_toDual_iff.mp hq
  · rintro ⟨p, hp, rfl⟩
    exact mem_selectFirstN_image_toDual_iff.mpr hp

theorem image_toDual_selectFirstN (N : ℕ) (s : Finset ι) :
    (selectFirstN N s).image OrderDual.toDual = selectLastN N (s.image OrderDual.toDual) := by
  ext q
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact mem_selectLastN_image_toDual_iff.mpr hp
  · intro hq
    have hq' : OrderDual.toDual (OrderDual.ofDual q) ∈
        selectLastN N (s.image OrderDual.toDual) := by
      simpa using hq
    exact ⟨OrderDual.ofDual q, mem_selectLastN_image_toDual_iff.mp hq', rfl⟩

theorem selectLastN_eq_image_selectFirstN (N : ℕ) (s : Finset ι) :
    selectLastN N s = (selectFirstN N (s.image OrderDual.toDual)).image OrderDual.ofDual := by
  rw [selectFirstN_image_toDual, Finset.image_image]
  simp

end Mirror

/-! ### The rightmost mechanism -/

/-- The rightmost rule keeps at most `N` candidates. Its exact cardinality is
proved below in `card_selectLastN`. -/
theorem selectLastN_card_le [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (selectLastN N s).card ≤ N := by
  classical
  by_contra h
  rw [not_le] at h
  have hne : (selectLastN N s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (selectLastN N s) (fun x => x) hne
  have hqrank : (s.filter fun p => q < p).card < N := (mem_selectLastN_iff.mp hq).2
  have hsub : (selectLastN N s).erase q ⊆ s.filter (fun p => q < p) := by
    intro p hp
    have hpt : p ∈ selectLastN N s := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    refine Finset.mem_filter.mpr ⟨(mem_selectLastN_iff.mp hpt).1, ?_⟩
    exact lt_of_le_of_ne (hmin p hpt) (Ne.symm hpq)
  have hle := Finset.card_le_card hsub
  have hcard := Finset.card_erase_add_one hq
  omega

theorem card_selectLastN [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (selectLastN N s).card = min N s.card := by
  classical
  rw [selectLastN_eq_image_selectFirstN,
    Finset.card_image_of_injective _ OrderDual.ofDual.injective,
    card_selectFirstN,
    Finset.card_image_of_injective _ OrderDual.toDual.injective]

/-- The greatest candidate survives the rightmost selection, and every
greatest candidate of the selection is greatest in the original candidate
set. -/
theorem isGreatest_selectLastN_iff [LinearOrder ι] {N : ℕ} (hN : 0 < N)
    {s : Finset ι} {x : ι} :
    IsGreatest (↑(selectLastN N s) : Set ι) x ↔ IsGreatest (↑s : Set ι) x := by
  classical
  constructor
  · intro hx
    have hxkeep : x ∈ selectLastN N s := by simpa using hx.1
    have hxs : x ∈ s := selectLastN_subset N s hxkeep
    have hxrank : (s.filter fun p => x < p).card < N := (mem_selectLastN_iff.mp hxkeep).2
    refine ⟨by simpa using hxs, ?_⟩
    intro y hy
    by_contra hle
    have hxy : x < y := lt_of_not_ge hle
    have hsub : s.filter (fun p => y < p) ⊆ s.filter (fun p => x < p) := by
      intro r hr
      obtain ⟨hrs, hyr⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrs, lt_trans hxy hyr⟩
    have hyrank : (s.filter fun p => y < p).card < N :=
      lt_of_le_of_lt (Finset.card_le_card hsub) hxrank
    have hykeep : y ∈ selectLastN N s :=
      mem_selectLastN_iff.mpr ⟨by simpa using hy, hyrank⟩
    exact absurd (hx.2 (by simpa using hykeep)) (not_le_of_gt hxy)
  · intro hx
    have hxmem : x ∈ s := by simpa using hx.1
    have hempty : s.filter (fun p => x < p) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hys, hxy⟩ := Finset.mem_filter.mp hy
      exact absurd (hx.2 (by simpa using hys)) (not_le_of_gt hxy)
    have hzero : (s.filter fun p => x < p).card = 0 := by
      rw [hempty]
      rfl
    refine ⟨by simpa using mem_selectLastN_iff.mpr ⟨hxmem, by rw [hzero]; exact hN⟩, ?_⟩
    intro y hy
    exact hx.2 (by simpa using selectLastN_subset N s (by simpa using hy))

/-- The rightmost selection mechanism of capacity `N`. -/
noncomputable def rightmost [LinearOrder ι] (N : ℕ) : FiniteNSelection ι N where
  select := selectLastN N
  subset := selectLastN_subset N
  card_eq := card_selectLastN N

@[simp] theorem rightmost_select [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (rightmost N).select s = selectLastN N s :=
  rfl

theorem rightmost_preservesGreatest [LinearOrder ι] {N : ℕ} (hN : 0 < N) :
    (rightmost (ι := ι) N).PreservesGreatest := by
  intro s x hx
  simpa using ((isGreatest_selectLastN_iff (N := N) hN).mpr hx).1

/-- Reversing the order turns the leftmost rule into the rightmost rule. -/
theorem leftmost_mapOrderDual [LinearOrder ι] [DecidableEq ι] (N : ℕ) :
    NSelection.mapOrderDual (leftmost (ι := ι) N) =
      (rightmost (ι := OrderDual ι) N) := by
  refine NSelection.ext fun s => ?_
  show (selectFirstN N (s.image OrderDual.ofDual)).image OrderDual.toDual = selectLastN N s
  rw [image_toDual_selectFirstN, Finset.image_image]
  simp

end NSelection end Selection

end Branching

end Combinatorics
