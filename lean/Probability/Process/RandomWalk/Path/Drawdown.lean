/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Fin.Basic
public import Probability.Process.RandomWalk.Path.Oscillation

import Mathlib.Tactic.FieldSimp

/-!
# Running maxima, drawdowns, and spatial bins

This file isolates the deterministic path geometry used to control a walk
with bounded historical drawdowns.  A running maximum is rounded upward to a
uniform spatial grid.  If its grid value does not change over a time block,
the path on that block lies in a fixed interval whose width is the drawdown
bound plus one grid cell.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The maximum value of a real sequence through the specified time. -/
noncomputable def prefixMaximum (path : ℕ → ℝ) (time : ℕ) : ℝ :=
  (Finset.range (time + 1)).sup'
    (by exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) path

theorem le_prefixMaximum (path : ℕ → ℝ) {i time : ℕ} (hi : i ≤ time) :
    path i ≤ prefixMaximum path time := by
  unfold prefixMaximum
  exact Finset.le_sup' path
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem prefixMaximum_le_of_forall (path : ℕ → ℝ) (time : ℕ) (upper : ℝ)
    (hupper : ∀ i ≤ time, path i ≤ upper) :
    prefixMaximum path time ≤ upper := by
  unfold prefixMaximum
  apply (Finset.sup'_le_iff
    (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ :
      (Finset.range (time + 1)).Nonempty) path).2
  intro i hi
  have hi' : i < time + 1 := Finset.mem_range.mp hi
  exact hupper i (Nat.le_of_lt_succ hi')

theorem prefixMaximum_mono (path : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    prefixMaximum path s ≤ prefixMaximum path t := by
  unfold prefixMaximum
  apply (Finset.sup'_le_iff
    (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ :
      (Finset.range (s + 1)).Nonempty) path).2
  intro i hi
  have hi' : i < s + 1 := Finset.mem_range.mp hi
  have hit : i ≤ t := (Nat.le_of_lt_succ hi').trans hst
  exact Finset.le_sup' path (Finset.mem_range.mpr (Nat.lt_succ_of_le hit))

/-- The spatial bin containing the running maximum when spatial bins have
width `width`. The bin is indexed downward from the deterministic ceiling
`upper`. -/
noncomputable def spatialBinIndex (upper width : ℝ) (path : ℕ → ℝ) (time : ℕ) : ℕ :=
  ⌊(upper - prefixMaximum path time) / width⌋₊

/-- The upper endpoint of the spatial bin containing the running maximum. -/
noncomputable def spatialBinLevel (upper width : ℝ) (path : ℕ → ℝ) (time : ℕ) : ℝ :=
  upper - width * (spatialBinIndex upper width path time : ℝ)

theorem prefixMaximum_le_spatialBinLevel
    (upper width : ℝ) (path : ℕ → ℝ) (time : ℕ)
    (hwidth : 0 < width) (hmax : prefixMaximum path time ≤ upper) :
    prefixMaximum path time ≤ spatialBinLevel upper width path time := by
  have hquot : 0 ≤ (upper - prefixMaximum path time) / width :=
    div_nonneg (sub_nonneg.mpr hmax) hwidth.le
  have hfloor := Nat.floor_le hquot
  have hmul := mul_le_mul_of_nonneg_left hfloor hwidth.le
  have hcancel : width * ((upper - prefixMaximum path time) / width) =
      upper - prefixMaximum path time := by
    field_simp [hwidth.ne']
  dsimp [spatialBinLevel, spatialBinIndex]
  rw [hcancel] at hmul
  linarith

theorem spatialBinLevel_lt_prefixMaximum_add_width
    (upper width : ℝ) (path : ℕ → ℝ) (time : ℕ)
    (hwidth : 0 < width) (hmax : prefixMaximum path time ≤ upper) :
    spatialBinLevel upper width path time <
      prefixMaximum path time + width := by
  have hquot : 0 ≤ (upper - prefixMaximum path time) / width :=
    div_nonneg (sub_nonneg.mpr hmax) hwidth.le
  have hfloor := Nat.lt_floor_add_one
    ((upper - prefixMaximum path time) / width)
  have hmul := mul_lt_mul_of_pos_left hfloor hwidth
  have hcancel : width * ((upper - prefixMaximum path time) / width) =
      upper - prefixMaximum path time := by
    field_simp [hwidth.ne']
  dsimp [spatialBinLevel, spatialBinIndex]
  rw [hcancel] at hmul
  nlinarith

theorem spatialBinIndex_antitone
    (upper width : ℝ) (path : ℕ → ℝ) {s t : ℕ}
    (hwidth : 0 < width) (hst : s ≤ t) :
    spatialBinIndex upper width path t ≤ spatialBinIndex upper width path s := by
  change ⌊(upper - prefixMaximum path t) / width⌋₊ ≤
    ⌊(upper - prefixMaximum path s) / width⌋₊
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hwidth.le
  exact sub_le_sub_left (prefixMaximum_mono path hst) upper

theorem spatialBinLevel_mono
    (upper width : ℝ) (path : ℕ → ℝ) {s t : ℕ}
    (hwidth : 0 < width) (hst : s ≤ t) :
    spatialBinLevel upper width path s ≤ spatialBinLevel upper width path t := by
  have hbin := spatialBinIndex_antitone upper width path hwidth hst
  dsimp [spatialBinLevel]
  have hbinCast :
      (spatialBinIndex upper width path t : ℝ) ≤
        (spatialBinIndex upper width path s : ℝ) := Nat.cast_le.mpr hbin
  have hmul := mul_le_mul_of_nonneg_left hbinCast hwidth.le
  linarith

theorem spatialBinIndex_le_of_zero
    (upper width : ℝ) (path : ℕ → ℝ) (time : ℕ)
    (hwidth : 0 < width) (hzero : path 0 = 0) :
    spatialBinIndex upper width path time ≤ ⌊upper / width⌋₊ := by
  have hmaxNonneg : 0 ≤ prefixMaximum path time := by
    calc
      0 = path 0 := hzero.symm
      _ ≤ prefixMaximum path time := le_prefixMaximum path (Nat.zero_le _)
  have hquot :
      (upper - prefixMaximum path time) / width ≤ upper / width := by
    apply div_le_div_of_nonneg_right _ hwidth.le
    exact sub_le_self upper hmaxNonneg
  exact Nat.floor_mono hquot

/-- On a block where the rounded running maximum is constant, a path with
drawdown at most `delta` is trapped in an interval of width
`width + delta`. -/
theorem values_between_on_constantSpatialBin
    (path : ℕ → ℝ) (upper width delta : ℝ)
    (hwidth : 0 < width)
    {horizon start finish : ℕ} (hstart : start ≤ finish)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      path i - path j ≤ delta)
    (hupper : ∀ i ≤ horizon, path i ≤ upper)
    (hfinish : finish ≤ horizon)
    (hbin : spatialBinLevel upper width path start =
      spatialBinLevel upper width path finish) :
    ∀ t, start ≤ t → t ≤ finish →
      spatialBinLevel upper width path start - width - delta < path t ∧
        path t ≤ spatialBinLevel upper width path start := by
  have hmaxStart : prefixMaximum path start ≤ upper :=
    prefixMaximum_le_of_forall path start upper (fun i hi => hupper i (by omega))
  have hmaxFinish : prefixMaximum path finish ≤ upper :=
    prefixMaximum_le_of_forall path finish upper (fun i hi => hupper i (by omega))
  have hroundedLower := spatialBinLevel_lt_prefixMaximum_add_width
    upper width path start hwidth hmaxStart
  intro t hst htt
  have hmaxMono : prefixMaximum path start ≤ prefixMaximum path t :=
    prefixMaximum_mono path hst
  have hmaxPath : prefixMaximum path t ≤ path t + delta := by
    apply prefixMaximum_le_of_forall path t (path t + delta)
    intro i hit
    have h := hnoDrop i t hit (htt.trans hfinish)
    linarith
  have hpathUpper : path t ≤ prefixMaximum path finish :=
    le_prefixMaximum path htt
  have hfinishUpper := prefixMaximum_le_spatialBinLevel
    upper width path finish hwidth hmaxFinish
  constructor
  · have hlowerStart :
        spatialBinLevel upper width path start - width <
          prefixMaximum path start := by
      linarith
    calc
      spatialBinLevel upper width path start - width - delta <
          prefixMaximum path start - delta := by linarith
      _ ≤ prefixMaximum path t - delta := sub_le_sub_right hmaxMono _
      _ ≤ path t := by linarith
  · calc
      path t ≤ prefixMaximum path finish := hpathUpper
      _ ≤ spatialBinLevel upper width path finish := hfinishUpper
      _ = spatialBinLevel upper width path start := hbin.symm

/-- A constant spatial bin also bounds the translation-invariant oscillation
of the path segment. This is the deterministic event consumed by independent
block estimates. -/
theorem oscillationBounded_on_constantSpatialBin
    (path : ℕ → ℝ) (upper width delta : ℝ)
    {horizon start length : ℕ}
    (hwidth : 0 < width)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      path i - path j ≤ delta)
    (hupper : ∀ i ≤ horizon, path i ≤ upper)
    (hfinish : start + length ≤ horizon)
    (hbin : spatialBinLevel upper width path start =
      spatialBinLevel upper width path (start + length)) :
    OscillationBounded
      (fun k : Fin (length + 1) => path (start + (k : ℕ)))
      (width + delta) := by
  intro i j
  have hi := values_between_on_constantSpatialBin path upper width delta
    hwidth (Nat.le_add_right start length) hnoDrop hupper hfinish hbin
    (start + (i : ℕ)) (Nat.le_add_right start _)
    (Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) _)
  have hj := values_between_on_constantSpatialBin path upper width delta
    hwidth (Nat.le_add_right start length) hnoDrop hupper hfinish hbin
    (start + (j : ℕ)) (Nat.le_add_right start _)
    (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) _)
  have hupperDiff : path (start + (i : ℕ)) - path (start + (j : ℕ)) ≤
      width + delta := by
    linarith [hi.2, hj.1]
  have hupperDiff' : path (start + (j : ℕ)) - path (start + (i : ℕ)) ≤
      width + delta := by
    linarith [hj.2, hi.1]
  rw [abs_le]
  constructor <;> linarith

/-- The times at which a binned running maximum changes. -/
def spatialBinJumpSet {q K : ℕ} (bins : Fin (q + 1) → Fin (K + 1)) :
    Finset (Fin q) :=
  Finset.univ.filter fun j => bins j.castSucc ≠ bins j.succ

/-- A nonincreasing sequence with `K+1` possible bin values can jump at most
`K+1` times. This loose bound is convenient for finite pattern counting. -/
theorem card_spatialBinJumpSet_le
    {q K : ℕ} (bins : Fin (q + 1) → Fin (K + 1))
    (hmono : ∀ i j, i ≤ j → bins j ≤ bins i) :
    (spatialBinJumpSet bins).card ≤ K + 1 := by
  classical
  let jumps := spatialBinJumpSet bins
  let target : Fin q → Fin (K + 1) := fun j => bins j.succ
  have hinj : Set.InjOn target (jumps : Set (Fin q)) := by
    intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have htime : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hmono' := hmono i.succ j.castSucc htime
      have hjump : bins j.succ < bins j.castSucc := by
        have hle := hmono j.castSucc j.succ (Fin.castSucc_le_succ j)
        have hne : bins j.castSucc ≠ bins j.succ := by
          simpa [jumps, spatialBinJumpSet] using hj
        exact lt_of_le_of_ne hle hne.symm
      change bins i.succ = bins j.succ at heq
      rw [heq] at hmono'
      exact (not_le_of_gt hjump) hmono'
    · have htime : j.succ ≤ i.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hmono' := hmono j.succ i.castSucc htime
      have hjump : bins i.succ < bins i.castSucc := by
        have hle := hmono i.castSucc i.succ (Fin.castSucc_le_succ i)
        have hne : bins i.castSucc ≠ bins i.succ := by
          simpa [jumps, spatialBinJumpSet] using hi
        exact lt_of_le_of_ne hle hne.symm
      change bins i.succ = bins j.succ at heq
      rw [← heq] at hmono'
      exact (not_le_of_gt hjump) hmono'
  have hcard : jumps.card ≤ (Finset.univ : Finset (Fin (K + 1))).card :=
    Finset.card_le_card_of_injOn target (by intro j hj; simp) hinj
  simpa [jumps] using hcard

/-- The blocks whose endpoint bin is unchanged are exactly the complement
of the jump set. -/
def spatialBinGoodBlockSet {q K : ℕ}
    (bins : Fin (q + 1) → Fin (K + 1)) : Finset (Fin q) :=
  Finset.univ.filter fun j => bins j.castSucc = bins j.succ

/-- Good blocks and jump blocks partition the finite block index set. -/
theorem card_spatialBinGoodBlockSet_add_jumpSet_card
    {q K : ℕ} (bins : Fin (q + 1) → Fin (K + 1)) :
    (spatialBinGoodBlockSet bins).card + (spatialBinJumpSet bins).card = q := by
  classical
  rw [spatialBinGoodBlockSet, spatialBinJumpSet]
  simpa using Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin q)))
    (fun j => bins j.castSucc = bins j.succ)

/-- A nonincreasing path through `K+1` spatial bins has at least `q-K-1`
unchanged-bin blocks. -/
theorem card_spatialBinGoodBlockSet_ge
    {q K : ℕ} (bins : Fin (q + 1) → Fin (K + 1))
    (hmono : ∀ i j, i ≤ j → bins j ≤ bins i) :
    q ≤ (spatialBinGoodBlockSet bins).card + (K + 1) := by
  have hpartition := card_spatialBinGoodBlockSet_add_jumpSet_card bins
  have hjumps := card_spatialBinJumpSet_le bins hmono
  omega

/-- A finite spatial-bin encoding of a no-large-drop path on a block
partition.  The bin indices are nonincreasing, and on each block where the
bin is unchanged the path stays in a deterministic interval of width
`delta + width`.  The finite range follows from the path starting at zero
and the deterministic upper bound. -/
theorem exists_spatialBinSequence_for_noLargeDrop
    (path : ℕ → ℝ) (upper width delta : ℝ)
    {horizon remainder blocks blockLength : ℕ}
    (hzero : path 0 = 0)
    (hwidth : 0 < width)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      path i - path j ≤ delta)
    (hupper : ∀ i ≤ horizon, path i ≤ upper)
    (hblocks : remainder + blocks * blockLength ≤ horizon) :
    ∃ bins : Fin (blocks + 1) → Fin (⌊upper / width⌋₊ + 1),
      (∀ i j, i ≤ j → bins j ≤ bins i) ∧
      (∀ j, (bins j : ℕ) = spatialBinIndex upper width path
        (remainder + j.val * blockLength)) ∧
      (∀ j : Fin blocks,
        bins j.castSucc = bins j.succ →
        ∀ k ≤ blockLength,
          spatialBinLevel upper width path
              (remainder + j.val * blockLength) - width - delta <
            path (remainder + j.val * blockLength + k) ∧
          path (remainder + j.val * blockLength + k) ≤
            spatialBinLevel upper width path
              (remainder + j.val * blockLength)) := by
  let binIndex : Fin (blocks + 1) → ℕ := fun j =>
    spatialBinIndex upper width path (remainder + j.val * blockLength)
  have hbinBound (j : Fin (blocks + 1)) : binIndex j ≤ ⌊upper / width⌋₊ := by
    apply spatialBinIndex_le_of_zero upper width path _ hwidth hzero
  let bins : Fin (blocks + 1) → Fin (⌊upper / width⌋₊ + 1) := fun j =>
    ⟨binIndex j, Nat.lt_succ_of_le (hbinBound j)⟩
  refine ⟨bins, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.le_iff_val_le_val.mpr
    dsimp [bins, binIndex]
    exact spatialBinIndex_antitone upper width path hwidth
      (Nat.add_le_add_left
        (Nat.mul_le_mul_right blockLength
          (Fin.le_iff_val_le_val.mp hij)) remainder)
  · intro j
    rfl
  · intro j hsame k hk
    have hstart : remainder + j.val * blockLength ≤
        remainder + (j.val + 1) * blockLength := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right blockLength (Nat.le_succ _)) _
    have hfinish : remainder + (j.val + 1) * blockLength ≤ horizon := by
      have hj : j.val + 1 ≤ blocks := Nat.succ_le_of_lt j.isLt
      have hmul := Nat.mul_le_mul_right blockLength hj
      exact (Nat.add_le_add_left hmul remainder).trans hblocks
    have hbinIndex : spatialBinIndex upper width path
          (remainder + j.val * blockLength) =
        spatialBinIndex upper width path
          (remainder + (j.val + 1) * blockLength) := by
      have hval := congrArg Fin.val hsame
      simpa [bins, binIndex, Fin.val_castSucc, Fin.val_succ] using hval
    have hlevel : spatialBinLevel upper width path
          (remainder + j.val * blockLength) =
        spatialBinLevel upper width path
          (remainder + (j.val + 1) * blockLength) := by
      simp [spatialBinLevel, hbinIndex]
    have htimeEq : remainder + j.val * blockLength + blockLength =
        remainder + (j.val + 1) * blockLength := by
      calc
        remainder + j.val * blockLength + blockLength =
            remainder + (j.val * blockLength + blockLength) := by omega
        _ = remainder + (j.val + 1) * blockLength := by
          rw [Nat.add_mul, one_mul]
    have hlevel' : spatialBinLevel upper width path
          (remainder + j.val * blockLength) =
        spatialBinLevel upper width path
          (remainder + j.val * blockLength + blockLength) := by
      rw [htimeEq]
      exact hlevel
    have hblockend :
        remainder + j.val * blockLength + blockLength ≤ horizon := by
      rw [htimeEq]
      exact hfinish
    have hstart' : remainder + j.val * blockLength ≤
        remainder + j.val * blockLength + blockLength := Nat.le_add_right _ _
    have hbetween := values_between_on_constantSpatialBin path upper width delta
      hwidth hstart' hnoDrop hupper hblockend hlevel'
    have htimeStart :
        remainder + j.val * blockLength ≤
          remainder + j.val * blockLength + k := Nat.le_add_right _ _
    have htimeEnd :
        remainder + j.val * blockLength + k ≤
            remainder + (j.val + 1) * blockLength := by
      calc
        remainder + j.val * blockLength + k ≤
            remainder + j.val * blockLength + blockLength :=
          Nat.add_le_add_left hk _
        _ = remainder + (j.val + 1) * blockLength := htimeEq
    rw [← htimeEq] at htimeEnd
    have hbound := hbetween
      (remainder + j.val * blockLength + k) htimeStart htimeEnd
    simpa [hlevel] using hbound

end ProbabilityTheory.RandomWalk

end
