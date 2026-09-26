import Combinatorics.BranchingWalk.Selection.NSelection.Basic
import Mathlib.Data.Finset.Max

/-!
# The leftmost selection mechanism

`keepFirst N s` really does keep at most `N` candidates when the candidate type
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

/-- The leftmost rule keeps at most `N` candidates. -/
theorem keepFirst_card_le [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (keepFirst N s).card ≤ N := by
  classical
  by_contra h
  rw [not_le] at h
  have hne : (keepFirst N s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image (keepFirst N s) (fun x => x) hne
  have hqrank : rank s q < N := (mem_keepFirst_iff.mp hq).2
  have hsub : (keepFirst N s).erase q ⊆ s.filter (fun p => p < q) := by
    intro p hp
    have hpt : p ∈ keepFirst N s := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    refine Finset.mem_filter.mpr ⟨(mem_keepFirst_iff.mp hpt).1, ?_⟩
    exact lt_of_le_of_ne (hmax p hpt) hpq
  have hle := Finset.card_le_card hsub
  have hcard := Finset.card_erase_add_one hq
  rw [rank] at hqrank
  omega

/-- The leftmost rule keeps the whole candidate set once it has at most `N`
candidates. -/
theorem keepFirst_eq_self_of_card_le [LinearOrder ι] {N : ℕ} {s : Finset ι}
    (h : s.card ≤ N) : keepFirst N s = s := by
  refine Finset.filter_true_of_mem fun q hq => ?_
  exact lt_of_lt_of_le (rank_lt_card_of_mem hq) h

theorem keepFirst_eq_self_iff_card_le [LinearOrder ι] {N : ℕ} {s : Finset ι} :
    keepFirst N s = s ↔ s.card ≤ N :=
  ⟨fun h => by
    rw [← h]
    exact keepFirst_card_le N s,
  fun h => keepFirst_eq_self_of_card_le h⟩

/-- Raising the capacity only adds candidates. -/
theorem keepFirst_mono [LinearOrder ι] {N M : ℕ} (h : N ≤ M) (s : Finset ι) :
    keepFirst N s ⊆ keepFirst M s := by
  intro q hq
  obtain ⟨hqs, hrank⟩ := mem_keepFirst_iff.mp hq
  exact mem_keepFirst_iff.mpr ⟨hqs, lt_of_lt_of_le hrank h⟩

/-- Selecting the leftmost `N` candidates is idempotent. -/
theorem keepFirst_idem [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepFirst N (keepFirst N s) = keepFirst N s := by
  classical
  have key : ∀ {q : ι}, q ∈ keepFirst N s → rank (keepFirst N s) q = rank s q := by
    intro q hq
    have hrankq : rank s q < N := (mem_keepFirst_iff.mp hq).2
    have hsub : s.filter (fun p => p < q) ⊆ (keepFirst N s).filter (fun p => p < q) := by
      intro p hp
      obtain ⟨hps, hpq⟩ := Finset.mem_filter.mp hp
      have hle : rank s p ≤ rank s q := by
        have hfilter : s.filter (fun r => r < p) ⊆ s.filter (fun r => r < q) := by
          intro r hr
          obtain ⟨hrs, hrp⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr ⟨hrs, lt_trans hrp hpq⟩
        simpa only [rank] using Finset.card_le_card hfilter
      exact Finset.mem_filter.mpr
        ⟨mem_keepFirst_iff.mpr ⟨hps, lt_of_le_of_lt hle hrankq⟩, hpq⟩
    have hfilter : (keepFirst N s).filter (fun p => p < q) = s.filter (fun p => p < q) := by
      refine Finset.Subset.antisymm ?_ hsub
      intro p hp
      obtain ⟨hpk, hpq⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨keepFirst_subset N s hpk, hpq⟩
    calc rank (keepFirst N s) q
        = ((keepFirst N s).filter (fun p => p < q)).card := rfl
      _ = (s.filter (fun p => p < q)).card := by rw [hfilter]
      _ = rank s q := rfl
  refine Finset.filter_true_of_mem fun q hq => ?_
  rw [key hq]
  exact (mem_keepFirst_iff.mp hq).2

/-- A nonempty candidate set has a nonempty leftmost selection as soon as the
capacity is positive. -/
theorem keepFirst_nonempty [LinearOrder ι] {N : ℕ} (hN : 0 < N) {s : Finset ι}
    (hs : s.Nonempty) : (keepFirst N s).Nonempty := by
  classical
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image s (fun x => x) hs
  refine ⟨q, mem_keepFirst_iff.mpr ⟨hq, ?_⟩⟩
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
theorem isLeast_keepFirst_iff [LinearOrder ι] {N : ℕ} (hN : 0 < N)
    {s : Finset ι} {x : ι} :
    IsLeast (↑(keepFirst N s) : Set ι) x ↔ IsLeast (↑s : Set ι) x := by
  classical
  constructor
  · intro hx
    have hxkeep : x ∈ keepFirst N s := by simpa using hx.1
    have hxs : x ∈ s := keepFirst_subset N s hxkeep
    have hxrank : rank s x < N := (mem_keepFirst_iff.mp hxkeep).2
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
    have hykeep : y ∈ keepFirst N s := mem_keepFirst_iff.mpr ⟨by simpa using hy, hyrank⟩
    exact absurd (hx.2 (by simpa using hykeep)) (not_le_of_gt hyx)
  · intro hx
    have hxmem : x ∈ s := by simpa using hx.1
    have hxrank : rank s x = 0 := (rank_eq_zero_iff_isLeast hxmem).mpr hx
    refine ⟨by simpa using mem_keepFirst_iff.mpr ⟨hxmem, by rw [hxrank]; exact hN⟩, ?_⟩
    intro y hy
    exact hx.2 (by simpa using keepFirst_subset N s (by simpa using hy))

/-- The leftmost selection mechanism of capacity `N`. -/
noncomputable def leftmost [LinearOrder ι] (N : ℕ) : NSelection ι N where
  select := keepFirst N
  subset := keepFirst_subset N
  card_le := keepFirst_card_le N

@[simp] theorem leftmost_select [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    (leftmost N).select s = keepFirst N s :=
  rfl

theorem leftmost_preservesLeast [LinearOrder ι] {N : ℕ} (hN : 0 < N) :
    (leftmost (ι := ι) N).PreservesLeast := by
  intro s x hx
  simpa using ((isLeast_keepFirst_iff (N := N) hN).mpr hx).1

end NSelection

end Selection

end Branching

end Combinatorics
