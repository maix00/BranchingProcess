import Combinatorics.BranchingWalk.Selection.NSelection.Basic
import Mathlib.Data.Finset.Max

/-!
# The leftmost selection mechanism

`selectFirstN N s` really does keep at most `N` candidates when the candidate type
is linearly ordered, and it keeps the least candidate. Idempotence and
monotonicity in the capacity are also proved here. The rightmost rule is the
order dual of this one and lives in `NSelection/OrderDual.lean`.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

namespace NSelection

variable {ι : Type*}

/-- A candidate has strictly smaller rank than the whole candidate set. -/
theorem rank_lt_card_of_mem [LinearOrder ι] {s : Finset ι} {q : ι} (hq : q ∈ s) :
    rank s q < s.card := by
  have hss : s.filter (fun p => p < q) ⊂ s :=
    Finset.filter_ssubset.mpr ⟨q, hq, lt_irrefl q⟩
  simpa [rank] using Finset.card_lt_card hss

/-- Strictly ordered candidates in one finite set have strictly ordered ranks. -/
theorem rank_lt_rank_of_lt [LinearOrder ι] {s : Finset ι} {p q : ι}
    (hp : p ∈ s) (hpq : p < q) : rank s p < rank s q := by
  classical
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.trans hpq⟩
  · intro hsub
    have : p ∈ s.filter fun r => r < q := Finset.mem_filter.mpr ⟨hp, hpq⟩
    exact (lt_irrefl p) (Finset.mem_filter.mp (hsub this)).2

/-- Rank is injective on the finite candidate set. -/
theorem rank_injOn [LinearOrder ι] (s : Finset ι) :
    Set.InjOn (rank s) ↑s := by
  intro p hp q hq heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · exact (ne_of_lt (rank_lt_rank_of_lt hp hpq)) heq
  · exact (ne_of_lt (rank_lt_rank_of_lt hq hqp)) heq.symm

/-- The ranks of a finite linearly ordered candidate set are exactly the
natural numbers below its cardinality. -/
theorem image_rank_eq_range [LinearOrder ι] (s : Finset ι) :
    s.image (rank s) = Finset.range s.card := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (rank_lt_card_of_mem hq)
  · rw [Finset.card_image_of_injOn (rank_injOn s), Finset.card_range]

/-- The leftmost rule keeps exactly the smaller of the capacity and the
candidate count. -/
theorem card_selectFirstN [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (selectFirstN N s).card = min N s.card := by
  classical
  have himage : (selectFirstN N s).image (rank s) = Finset.range (min N s.card) := by
    ext k
    simp only [Finset.mem_image, mem_selectFirstN_iff, Finset.mem_range]
    constructor
    · rintro ⟨q, ⟨hqs, hqN⟩, rfl⟩
      exact lt_min hqN (rank_lt_card_of_mem hqs)
    · intro hk
      have hks : k ∈ Finset.range s.card := Finset.mem_range.mpr (lt_of_lt_of_le hk (min_le_right _ _))
      rw [← image_rank_eq_range s] at hks
      obtain ⟨q, hqs, hqrank⟩ := Finset.mem_image.mp hks
      refine ⟨q, ⟨hqs, ?_⟩, hqrank⟩
      rw [hqrank]
      exact lt_of_lt_of_le hk (min_le_left _ _)
  calc
    (selectFirstN N s).card = ((selectFirstN N s).image (rank s)).card := by
      symm
      apply Finset.card_image_of_injOn
      exact (rank_injOn s).mono (fun _ h => selectFirstN_subset N s h)
    _ = (Finset.range (min N s.card)).card := congrArg Finset.card himage
    _ = min N s.card := Finset.card_range _

/-- Intersecting a leftmost selection with a lower set keeps exactly the
smaller of the capacity and the number of candidates in that lower set.  The
predicate only has to be downward closed on the supplied finite set. -/
theorem card_filter_selectFirstN_of_downwardClosed [LinearOrder ι]
    (N : ℕ) (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (hdown : ∀ ⦃p q : ι⦄, p ∈ s → q ∈ s → q ≤ p → P p → P q) :
    ((selectFirstN N s).filter P).card = min N (s.filter P).card := by
  classical
  have heq : (selectFirstN N s).filter P =
      selectFirstN (min N (s.filter P).card) s := by
    ext q
    simp only [Finset.mem_filter, mem_selectFirstN_iff]
    constructor
    · rintro ⟨⟨hqs, hqN⟩, hqP⟩
      refine ⟨hqs, lt_min hqN ?_⟩
      have hsub : insert q (s.filter fun p => p < q) ⊆ s.filter P := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact Finset.mem_filter.mpr ⟨hqs, hqP⟩
        · obtain ⟨hps, hpq⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨hps, hdown hqs hps (le_of_lt hpq) hqP⟩
      have hnot : q ∉ s.filter fun p => p < q := by simp
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hcard
      exact Nat.lt_of_succ_le hcard
    · rintro ⟨hqs, hqrank⟩
      refine ⟨⟨hqs, lt_of_lt_of_le hqrank (min_le_left _ _)⟩, ?_⟩
      by_contra hnP
      have hsub : s.filter P ⊆ s.filter fun p => p < q := by
        intro p hp
        obtain ⟨hps, hpP⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨hps, ?_⟩
        rcases lt_trichotomy p q with hpq | rfl | hqp
        · exact hpq
        · exact (hnP hpP).elim
        · exact (hnP (hdown hps hqs (le_of_lt hqp) hpP)).elim
      have hle := Finset.card_le_card hsub
      exact (not_le_of_gt (lt_of_lt_of_le hqrank (min_le_right _ _))) hle
  rw [heq, card_selectFirstN]
  exact min_eq_left (le_trans (min_le_right _ _) (Finset.card_filter_le s P))

/-- The rank of a candidate vanishes exactly when the candidate is least. -/
theorem rank_eq_zero_iff_isLeast [LinearOrder ι] {s : Finset ι} {x : ι}
    (hx : x ∈ s) :
    rank s x = 0 ↔ IsLeast (↑s : Set ι) x := by
  constructor
  · intro h
    refine ⟨by simpa using hx, ?_⟩
    intro y hy
    by_contra hle
    have hyx : y < x := lt_of_not_ge hle
    have hymem : y ∈ s.filter (fun p => p < x) :=
      Finset.mem_filter.mpr ⟨by simpa using hy, hyx⟩
    have hzero : (s.filter (fun p => p < x)).card = 0 := by
      simpa [rank] using h
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hymem
    exact absurd hymem (by simp)
  · intro h
    have hempty : s.filter (fun p => p < x) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hys, hyx⟩ := Finset.mem_filter.mp hy
      exact absurd (h.2 (by simpa using hys)) (not_le_of_gt hyx)
    simp [rank, hempty]

/-- The leftmost rule keeps at most `N` candidates. Its exact cardinality is
proved below in `card_selectFirstN`. -/
theorem selectFirstN_card_le [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (selectFirstN N s).card ≤ N := by
  classical
  by_contra h
  rw [not_le] at h
  have hne : (selectFirstN N s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image (selectFirstN N s) (fun x => x) hne
  have hqrank : rank s q < N := (mem_selectFirstN_iff.mp hq).2
  have hsub : (selectFirstN N s).erase q ⊆ s.filter (fun p => p < q) := by
    intro p hp
    have hpt : p ∈ selectFirstN N s := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    refine Finset.mem_filter.mpr ⟨(mem_selectFirstN_iff.mp hpt).1, ?_⟩
    exact lt_of_le_of_ne (hmax p hpt) hpq
  have hle := Finset.card_le_card hsub
  have hcard := Finset.card_erase_add_one hq
  rw [rank] at hqrank
  omega

/-- The leftmost rule keeps the whole candidate set once it has at most `N`
candidates. -/
theorem selectFirstN_eq_self_of_card_le [LinearOrder ι] {N : ℕ} {s : Finset ι}
    (h : s.card ≤ N) : selectFirstN N s = s := by
  refine Finset.filter_true_of_mem fun q hq => ?_
  exact lt_of_lt_of_le (rank_lt_card_of_mem hq) h

theorem selectFirstN_eq_self_iff_card_le [LinearOrder ι] {N : ℕ} {s : Finset ι} :
    selectFirstN N s = s ↔ s.card ≤ N :=
  ⟨fun h => by
    rw [← h]
    exact selectFirstN_card_le N s,
  fun h => selectFirstN_eq_self_of_card_le h⟩

/-- Raising the capacity only adds candidates. -/
theorem selectFirstN_mono [LinearOrder ι] {N M : ℕ} (h : N ≤ M) (s : Finset ι) :
    selectFirstN N s ⊆ selectFirstN M s := by
  intro q hq
  obtain ⟨hqs, hrank⟩ := mem_selectFirstN_iff.mp hq
  exact mem_selectFirstN_iff.mpr ⟨hqs, lt_of_lt_of_le hrank h⟩

/-- Selecting the leftmost `N` candidates is idempotent. -/
theorem selectFirstN_idem [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    selectFirstN N (selectFirstN N s) = selectFirstN N s := by
  classical
  have key : ∀ {q : ι}, q ∈ selectFirstN N s → rank (selectFirstN N s) q = rank s q := by
    intro q hq
    have hrankq : rank s q < N := (mem_selectFirstN_iff.mp hq).2
    have hsub : s.filter (fun p => p < q) ⊆ (selectFirstN N s).filter (fun p => p < q) := by
      intro p hp
      obtain ⟨hps, hpq⟩ := Finset.mem_filter.mp hp
      have hle : rank s p ≤ rank s q := by
        have hfilter : s.filter (fun r => r < p) ⊆ s.filter (fun r => r < q) := by
          intro r hr
          obtain ⟨hrs, hrp⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr ⟨hrs, lt_trans hrp hpq⟩
        simpa only [rank] using Finset.card_le_card hfilter
      exact Finset.mem_filter.mpr
        ⟨mem_selectFirstN_iff.mpr ⟨hps, lt_of_le_of_lt hle hrankq⟩, hpq⟩
    have hfilter : (selectFirstN N s).filter (fun p => p < q) = s.filter (fun p => p < q) := by
      refine Finset.Subset.antisymm ?_ hsub
      intro p hp
      obtain ⟨hpk, hpq⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨selectFirstN_subset N s hpk, hpq⟩
    calc rank (selectFirstN N s) q
        = ((selectFirstN N s).filter (fun p => p < q)).card := rfl
      _ = (s.filter (fun p => p < q)).card := by rw [hfilter]
      _ = rank s q := rfl
  refine Finset.filter_true_of_mem fun q hq => ?_
  rw [key hq]
  exact (mem_selectFirstN_iff.mp hq).2

/-- A nonempty candidate set has a nonempty leftmost selection as soon as the
capacity is positive. -/
theorem selectFirstN_nonempty [LinearOrder ι] {N : ℕ} (hN : 0 < N) {s : Finset ι}
    (hs : s.Nonempty) : (selectFirstN N s).Nonempty := by
  classical
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image s (fun x => x) hs
  refine ⟨q, mem_selectFirstN_iff.mpr ⟨hq, ?_⟩⟩
  have hempty : s.filter (fun p => p < q) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨hps, hpq⟩ := Finset.mem_filter.mp hp
    exact absurd (hmin p hps) (not_le_of_gt hpq)
  have hzero : rank s q = 0 := by
    rw [rank, hempty]
    rfl
  rw [hzero]
  exact hN

/-- The least candidate survives the leftmost selection, and every least
candidate of the selection is least in the original candidate set. -/
theorem isLeast_selectFirstN_iff [LinearOrder ι] {N : ℕ} (hN : 0 < N)
    {s : Finset ι} {x : ι} :
    IsLeast (↑(selectFirstN N s) : Set ι) x ↔ IsLeast (↑s : Set ι) x := by
  classical
  constructor
  · intro hx
    have hxkeep : x ∈ selectFirstN N s := by simpa using hx.1
    have hxs : x ∈ s := selectFirstN_subset N s hxkeep
    have hxrank : rank s x < N := (mem_selectFirstN_iff.mp hxkeep).2
    refine ⟨by simpa using hxs, ?_⟩
    intro y hy
    by_contra hle
    have hyx : y < x := lt_of_not_ge hle
    have hsub : s.filter (fun p => p < y) ⊆ s.filter (fun p => p < x) := by
      intro r hr
      obtain ⟨hrs, hry⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrs, lt_trans hry hyx⟩
    have hyrank : rank s y < N := by
      have hle' : (s.filter (fun p => p < y)).card ≤ (s.filter (fun p => p < x)).card :=
        Finset.card_le_card hsub
      have hle'' : rank s y ≤ rank s x := by
        simpa only [rank] using hle'
      exact lt_of_le_of_lt hle'' hxrank
    have hykeep : y ∈ selectFirstN N s := mem_selectFirstN_iff.mpr ⟨by simpa using hy, hyrank⟩
    exact absurd (hx.2 (by simpa using hykeep)) (not_le_of_gt hyx)
  · intro hx
    have hxmem : x ∈ s := by simpa using hx.1
    have hxrank : rank s x = 0 := (rank_eq_zero_iff_isLeast hxmem).mpr hx
    refine ⟨by simpa using mem_selectFirstN_iff.mpr ⟨hxmem, by rw [hxrank]; exact hN⟩, ?_⟩
    intro y hy
    exact hx.2 (by simpa using selectFirstN_subset N s (by simpa using hy))

/-- The leftmost selection mechanism of capacity `N`. -/
noncomputable def leftmost [LinearOrder ι] (N : ℕ) : NSelection ι N where
  select := selectFirstN N
  subset := selectFirstN_subset N
  card_eq := card_selectFirstN N

@[simp] theorem leftmost_select [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (leftmost N).select s = selectFirstN N s :=
  rfl

theorem leftmost_preservesLeast [LinearOrder ι] {N : ℕ} (hN : 0 < N) :
    (leftmost (ι := ι) N).PreservesLeast := by
  intro s x hx
  simpa using ((isLeast_selectFirstN_iff (N := N) hN).mpr hx).1

end NSelection

end Selection

end Branching

end Combinatorics
