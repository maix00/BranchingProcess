/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

/-!
# Integer block scales

This file contains the rounding and quotient facts shared by the diffusive
and stable small-deviation constructions.  The probabilistic scale
parameters remain in their respective modules; only the common floor
operation and its asymptotic interface live here.
-/

public section

open Filter Topology

namespace Asymptotics

/-- The integer length obtained by rounding a real-valued block argument
down at each time. -/
@[expose] noncomputable def floorBlockLength (argument : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊argument n⌋₊

/-- A divergent nonnegative block argument has a divergent rounded length. -/
theorem tendsto_floorBlockLength_atTop {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (floorBlockLength argument) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp hargument

/-- A divergent rounded block length is eventually positive. -/
theorem eventually_floorBlockLength_pos {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    ∀ᶠ n in atTop, 0 < floorBlockLength argument n :=
  (tendsto_floorBlockLength_atTop hargument).eventually
    (eventually_gt_atTop 0)

/-- Rounding a positive divergent argument does not change its normalized
length. -/
theorem tendsto_floorBlockLength_div_argument {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (fun n => (floorBlockLength argument n : ℝ) / argument n)
      atTop (nhds 1) :=
  (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument

/-- Rounding a fixed nonnegative fraction of the horizon down to an integer
does not change its asymptotic proportion. This is the time-coordinate
version of the floor block-length estimate. -/
theorem tendsto_floorTime_div_nat {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => (floorBlockLength (fun n => (n : ℝ) * t) n : ℝ) /
      (n : ℝ)) atTop (nhds t) := by
  by_cases ht0 : t = 0
  · subst t
    have heq : (fun n => (floorBlockLength (fun n => (n : ℝ) * (0 : ℝ)) n : ℝ) /
        (n : ℝ)) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [] with n
      simp [floorBlockLength]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr' heq.symm
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let argument : ℕ → ℝ := fun n => (n : ℝ) * t
    have hargument : Tendsto argument atTop atTop := by
      simpa [argument, mul_comm] using
        tendsto_natCast_atTop_atTop.const_mul_atTop htpos
    have hfloor := tendsto_floorBlockLength_div_argument hargument
    have hargumentDiv : Tendsto (fun n => argument n / (n : ℝ))
        atTop (nhds t) := by
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (nhds t)).congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp [argument, hnNe]
    have hproduct := hfloor.mul hargumentDiv
    have heq : (fun n => (floorBlockLength argument n : ℝ) /
        (n : ℝ)) =ᶠ[atTop] fun n =>
          ((floorBlockLength argument n : ℝ) / argument n) *
            (argument n / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hargNe : argument n ≠ 0 := by
        dsimp [argument]
        exact mul_ne_zero hnNe ht0
      field_simp [hnNe, hargNe]
    have hresult := hproduct.congr' heq.symm
    simpa using hresult

/-- The number of integer times in a real partition cell, using the source's
floor convention at both endpoints, has the cell's limiting duration. -/
theorem tendsto_floorSegmentLength_div_nat {left right : ℝ}
    (hleft : 0 ≤ left) (hle : left ≤ right) :
    Tendsto (fun n =>
      ((floorBlockLength (fun n => (n : ℝ) * right) n -
        floorBlockLength (fun n => (n : ℝ) * left) n : ℕ) : ℝ) /
        (n : ℝ)) atTop (nhds (right - left)) := by
  have hleftLimit := tendsto_floorTime_div_nat hleft
  have hrightLimit := tendsto_floorTime_div_nat (le_trans hleft hle)
  have hdiff := hrightLimit.sub hleftLimit
  have hfloorOrder : ∀ n,
      floorBlockLength (fun n => (n : ℝ) * left) n ≤
        floorBlockLength (fun n => (n : ℝ) * right) n := by
    intro n
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n)
  have heq : (fun n =>
      ((floorBlockLength (fun n => (n : ℝ) * right) n -
        floorBlockLength (fun n => (n : ℝ) * left) n : ℕ) : ℝ) /
        (n : ℝ)) =ᶠ[atTop] fun n =>
          (floorBlockLength (fun n => (n : ℝ) * right) n : ℝ) /
            (n : ℝ) -
          (floorBlockLength (fun n => (n : ℝ) * left) n : ℝ) /
            (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Nat.cast_sub (hfloorOrder n)]
    ring
  have hresult := hdiff.congr' heq.symm
  simpa using hresult

/-- Removing one terminal position from a floor-rounded interval does not
change its asymptotic time proportion. This is the half-open convention used
when a jump at the right endpoint belongs to the next partition cell. -/
theorem tendsto_floorSegmentLength_sub_one_div_nat {left right : ℝ}
    (hleft : 0 ≤ left) (hle : left < right) :
    Tendsto (fun n =>
      ((floorBlockLength (fun n => (n : ℝ) * right) n -
        floorBlockLength (fun n => (n : ℝ) * left) n - 1 : ℕ) : ℝ) /
          (n : ℝ)) atTop (nhds (right - left)) := by
  let length : ℕ → ℕ := fun n =>
    floorBlockLength (fun n => (n : ℝ) * right) n -
      floorBlockLength (fun n => (n : ℝ) * left) n
  have hlengthRatio : Tendsto (fun n => (length n : ℝ) / (n : ℝ))
      atTop (nhds (right - left)) := by
    simpa [length] using tendsto_floorSegmentLength_div_nat hleft (le_of_lt hle)
  have hlengthPos : ∀ᶠ n in atTop, 0 < length n := by
    have hratioPos : ∀ᶠ n in atTop, 0 < (length n : ℝ) / (n : ℝ) :=
      hlengthRatio.eventually (Ioi_mem_nhds (sub_pos.mpr hle))
    filter_upwards [hratioPos, eventually_gt_atTop (0 : ℕ)] with n hratio hn
    by_contra hzero
    have hlenZero : length n = 0 := Nat.eq_zero_of_not_pos hzero
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    simp [hlenZero] at hratio
  have hsub : (fun n => ((length n - 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
      fun n => (length n : ℝ) / (n : ℝ) - (1 : ℝ) / (n : ℝ) := by
    filter_upwards [hlengthPos, eventually_gt_atTop (0 : ℕ)] with n hpos hn
    have hcast : (length n - 1 : ℕ) = (length n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
      simp
    rw [hcast]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    ring
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hresult := hlengthRatio.sub hinv
  have hresult' : Tendsto
      (fun n => (length n : ℝ) / (n : ℝ) - (1 : ℝ) / (n : ℝ))
      atTop (nhds (right - left)) := by
    convert hresult using 1 <;> simp
  have hfinal := hresult'.congr' hsub.symm
  simpa [length] using hfinal

/-- The rounded length is bounded above by its argument whenever the latter
is nonnegative. -/
theorem floorBlockLength_le {argument : ℕ → ℝ} {n : ℕ}
    (hargument : 0 ≤ argument n) :
    (floorBlockLength argument n : ℝ) ≤ argument n :=
  Nat.floor_le hargument

/-- If the real ratio of two natural sequences tends to infinity and the
denominator is eventually positive, then their natural quotient tends to
infinity as well. -/
theorem tendsto_nat_div_atTop_of_cast_ratio
    {a b : ℕ → ℕ}
    (hb : ∀ᶠ n : ℕ in atTop, 0 < b n)
    (hratio : Tendsto (fun n => (a n : ℝ) / (b n : ℝ)) atTop atTop) :
    Tendsto (fun n => a n / b n) atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  have hratioK : ∀ᶠ n : ℕ in atTop,
      (k : ℝ) ≤ (a n : ℝ) / (b n : ℝ) :=
    hratio.eventually (eventually_ge_atTop (k : ℝ))
  filter_upwards [hb, hratioK] with n hb hratioK
  by_contra hnot
  have hdiv : a n / b n < k := Nat.lt_of_not_ge hnot
  have hmul : a n < k * b n := (Nat.div_lt_iff_lt_mul hb).1 hdiv
  have hmulReal : (a n : ℝ) < (k : ℝ) * (b n : ℝ) := by exact_mod_cast hmul
  have hmulLower : (k : ℝ) * (b n : ℝ) ≤ (a n : ℝ) :=
    (le_div_iff₀ (by exact_mod_cast hb)).1 hratioK
  linarith

/-- If a horizon has positive asymptotic density while a positive reference
block has vanishing density, the number of reference blocks in the horizon
tends to infinity. -/
theorem tendsto_nat_div_atTop_of_positive_horizonRatio_of_zero_blockRatio
    {total referenceLength : ℕ → ℕ} {duration : ℝ}
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ)) atTop (nhds duration))
    (hduration : 0 < duration)
    (hreference : Tendsto
      (fun n => (referenceLength n : ℝ) / (n : ℝ)) atTop (nhds 0))
    (hreferencePos : ∀ᶠ n : ℕ in atTop, 0 < referenceLength n) :
    Tendsto (fun n => total n / referenceLength n) atTop atTop := by
  have htotalPos : ∀ᶠ n : ℕ in atTop,
      0 < (total n : ℝ) / (n : ℝ) :=
    htotal.eventually (Ioi_mem_nhds hduration)
  have hreferenceRatioPos : ∀ᶠ n : ℕ in atTop,
      0 < (referenceLength n : ℝ) / (n : ℝ) := by
    filter_upwards [hreferencePos, eventually_gt_atTop (0 : ℕ)] with n hlength hn
    exact div_pos (Nat.cast_pos.mpr hlength) (Nat.cast_pos.mpr hn)
  have hreferenceWithin : Tendsto
      (fun n => (referenceLength n : ℝ) / (n : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hreference, hreferenceRatioPos⟩
  have hinv : Tendsto
      (fun n => ((referenceLength n : ℝ) / (n : ℝ))⁻¹) atTop atTop :=
    hreferenceWithin.inv_tendsto_nhdsGT_zero
  have hratio : Tendsto
      (fun n => ((total n : ℝ) / (n : ℝ)) *
        ((referenceLength n : ℝ) / (n : ℝ))⁻¹) atTop atTop :=
    htotal.pos_mul_atTop hduration hinv
  have hratio' : Tendsto
      (fun n => (total n : ℝ) / (referenceLength n : ℝ)) atTop atTop := by
    apply hratio.congr'
    filter_upwards [hreferencePos, eventually_gt_atTop (0 : ℕ)] with n hlength hn
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlengthNe : (referenceLength n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [hnNe, hlengthNe]
  exact tendsto_nat_div_atTop_of_cast_ratio hreferencePos hratio'

/-- A vanishing-density block is eventually no longer than a horizon with
positive limiting density. -/
theorem eventually_block_le_horizon_of_positive_density
    {total block : ℕ → ℕ} {duration : ℝ}
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ)) atTop (nhds duration))
    (hblock : Tendsto (fun n => (block n : ℝ) / (n : ℝ)) atTop (nhds 0))
    (hduration : 0 < duration) :
    ∀ᶠ n : ℕ in atTop, block n ≤ total n := by
  have htotalLower : ∀ᶠ n : ℕ in atTop,
      duration / 2 < (total n : ℝ) / (n : ℝ) :=
    htotal.eventually (Ioi_mem_nhds (by linarith))
  have hblockUpper : ∀ᶠ n : ℕ in atTop,
      (block n : ℝ) / (n : ℝ) < duration / 2 :=
    hblock.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [htotalLower, hblockUpper, eventually_gt_atTop (0 : ℕ)]
    with n htotalN hblockN hn
  by_contra hnot
  have hnat : total n < block n := Nat.lt_of_not_ge hnot
  have hreal : (total n : ℝ) < (block n : ℝ) := by exact_mod_cast hnat
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hratio : (total n : ℝ) / (n : ℝ) <
      (block n : ℝ) / (n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnReal).2 hreal
  linarith

/-- Removing a block of vanishing relative length does not change the
positive limiting density of a natural-number horizon. -/
theorem tendsto_nat_sub_div_nat_of_horizon_and_vanishingBlock
    {total block : ℕ → ℕ} {duration : ℝ}
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ)) atTop (nhds duration))
    (hblock : Tendsto (fun n => (block n : ℝ) / (n : ℝ)) atTop (nhds 0))
    (hduration : 0 < duration) :
    Tendsto (fun n => ((total n - block n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds duration) := by
  have hblockLe := eventually_block_le_horizon_of_positive_density
    htotal hblock hduration
  have hcongr :
      (fun n => ((total n - block n : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (total n : ℝ) / (n : ℝ) - (block n : ℝ) / (n : ℝ) := by
    filter_upwards [hblockLe, eventually_gt_atTop (0 : ℕ)] with n hle hn
    rw [Nat.cast_sub hle]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hn']
  have hsub := htotal.sub hblock
  have hsub' : Tendsto
      (fun n => (total n : ℝ) / (n : ℝ) - (block n : ℝ) / (n : ℝ))
      atTop (nhds duration) := by simpa using hsub
  exact hsub'.congr' hcongr.symm

/-! ## Exact balanced partitions -/

/-- The number of blocks in the balanced partition of `total` relative to a
reference length. -/
@[expose] def balancedBlockCount (total referenceLength : ℕ) : ℕ :=
  total / referenceLength

/-- The shorter of the two block lengths in a balanced partition. -/
@[expose] def balancedBlockShortLength (total referenceLength : ℕ) : ℕ :=
  referenceLength +
    (total % referenceLength) / balancedBlockCount total referenceLength

/-- The remainder after fitting reference blocks in the horizon. -/
@[expose] def balancedBlockRemainder (total referenceLength : ℕ) : ℕ :=
  total % referenceLength

/-- The number of blocks which use the longer of the two balanced lengths. -/
@[expose] def balancedBlockLongCount (total referenceLength : ℕ) : ℕ :=
  balancedBlockRemainder total referenceLength %
    balancedBlockCount total referenceLength

/-- Split `total` into blocks of two consecutive lengths, distributing the
remainder evenly. When the reference block count is positive, the list has
exactly `total / referenceLength` entries and its lengths sum to `total`. -/
@[expose] def balancedBlockLengths (total referenceLength : ℕ) : List ℕ :=
  List.replicate
      (balancedBlockCount total referenceLength -
        balancedBlockLongCount total referenceLength)
      (balancedBlockShortLength total referenceLength) ++
    List.replicate (balancedBlockLongCount total referenceLength)
      (balancedBlockShortLength total referenceLength + 1)

/-- The balanced partition has exactly the reference quotient many blocks. -/
theorem balancedBlockLengths_length {total referenceLength : ℕ}
    (hcount : 0 < balancedBlockCount total referenceLength) :
    (balancedBlockLengths total referenceLength).length =
      balancedBlockCount total referenceLength := by
  have hrem : balancedBlockLongCount total referenceLength <
      balancedBlockCount total referenceLength := by
    dsimp [balancedBlockLongCount, balancedBlockRemainder,
      balancedBlockCount]
    exact Nat.mod_lt (total % referenceLength) hcount
  simp [balancedBlockLengths, List.length_replicate,
    Nat.sub_add_cancel hrem.le]

/-- The balanced partition covers the horizon exactly, with no discarded
remainder. -/
theorem balancedBlockLengths_sum {total referenceLength : ℕ}
    (hcount : 0 < balancedBlockCount total referenceLength) :
    (balancedBlockLengths total referenceLength).sum = total := by
  let q := balancedBlockCount total referenceLength
  let r := balancedBlockLongCount total referenceLength
  let s := balancedBlockShortLength total referenceLength
  have hr : r < q := by
    dsimp [r, q, balancedBlockLongCount, balancedBlockRemainder,
      balancedBlockCount]
    exact Nat.mod_lt (total % referenceLength) hcount
  have hrem :
      q * ((total % referenceLength) / q) + r = total % referenceLength := by
    dsimp [q, r, balancedBlockLongCount, balancedBlockRemainder,
      balancedBlockCount]
    exact Nat.div_add_mod (total % referenceLength) _
  have hdiv : q * referenceLength + total % referenceLength = total := by
    dsimp [q, balancedBlockCount]
    simpa [Nat.mul_comm] using Nat.div_add_mod total referenceLength
  change (List.replicate (q - r) s ++ List.replicate r (s + 1)).sum = total
  rw [List.sum_append, List.sum_replicate, List.sum_replicate]
  calc
    (q - r) * s + r * (s + 1) = q * s + r := by
      rw [Nat.mul_add]
      simp only [Nat.mul_one]
      calc
        (q - r) * s + (r * s + r) =
            ((q - r) + r) * s + r := by
          calc
            (q - r) * s + (r * s + r) =
                ((q - r) * s + r * s) + r := by ac_rfl
            _ = ((q - r) + r) * s + r := by rw [← Nat.add_mul]
        _ = q * s + r := by rw [Nat.sub_add_cancel hr.le]
    _ = total := by
      calc
        q * s + r =
            q * referenceLength +
              (q * ((total % referenceLength) / q) + r) := by
          change q * (referenceLength + (total % referenceLength) / q) + r = _
          rw [Nat.mul_add]
          ac_rfl
        _ = q * referenceLength + total % referenceLength := by rw [hrem]
        _ = total := hdiv

/-- Every balanced block is one of the two adjacent integer lengths around
the average. -/
theorem mem_balancedBlockLengths {total referenceLength length : ℕ}
    (hmem : length ∈ balancedBlockLengths total referenceLength) :
    length = balancedBlockShortLength total referenceLength ∨
      length = balancedBlockShortLength total referenceLength + 1 := by
  simp only [balancedBlockLengths, List.mem_append, List.mem_replicate] at hmem
  rcases hmem with ⟨_, hlen⟩ | ⟨_, hlen⟩
  · exact Or.inl hlen
  · exact Or.inr hlen

/-- If the reference length and the number of reference blocks both diverge,
the shorter balanced length is asymptotic to the reference length. -/
theorem tendsto_balancedBlockShortLength_div_referenceLength
    {total referenceLength : ℕ → ℕ}
    (href : Tendsto (fun n => (referenceLength n : ℝ)) atTop atTop)
    (hcount : Tendsto
      (fun n => (balancedBlockCount (total n) (referenceLength n) : ℝ))
      atTop atTop) :
    Tendsto
      (fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ)) atTop (nhds 1) := by
  let q : ℕ → ℕ := fun n => balancedBlockCount (total n) (referenceLength n)
  let r : ℕ → ℕ := fun n => balancedBlockRemainder (total n) (referenceLength n)
  let extra : ℕ → ℕ := fun n => r n / q n
  let error : ℕ → ℝ := fun n => (extra n : ℝ) / (referenceLength n : ℝ)
  have hqPos : ∀ᶠ n in atTop, 0 < q n := by
    filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with n hn
    exact_mod_cast hn
  have hrefPos : ∀ᶠ n in atTop, 0 < referenceLength n := by
    filter_upwards [href.eventually (eventually_gt_atTop 0)] with n hn
    exact_mod_cast hn
  have herrorNonneg : ∀ᶠ n in atTop, 0 ≤ error n := by
    filter_upwards [hrefPos] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have herrorBound : ∀ᶠ n in atTop, error n ≤ 1 / (q n : ℝ) := by
    filter_upwards [hqPos, hrefPos] with n hq hn
    have hqR : 0 < (q n : ℝ) := by exact_mod_cast hq
    have hrefR : 0 < (referenceLength n : ℝ) := by exact_mod_cast hn
    have hr : r n ≤ referenceLength n := by
      dsimp [r, balancedBlockRemainder]
      exact Nat.le_of_lt (Nat.mod_lt _ hn)
    have hcast : (extra n : ℝ) ≤ (r n : ℝ) / (q n : ℝ) := by
      dsimp [extra]
      exact Nat.cast_div_le
    have hquot : (r n : ℝ) / (q n : ℝ) ≤
        (referenceLength n : ℝ) / (q n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hr)
        (Nat.cast_nonneg (q n))
    calc
      error n ≤ ((r n : ℝ) / (q n : ℝ)) / (referenceLength n : ℝ) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      _ ≤ ((referenceLength n : ℝ) / (q n : ℝ)) /
          (referenceLength n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hquot
          (inv_nonneg.mpr hrefR.le)
        simpa [div_eq_mul_inv] using hmul
      _ = 1 / (q n : ℝ) := by field_simp [hqR.ne', hrefR.ne']
  have hqTop : Tendsto (fun n => (q n : ℝ)) atTop atTop := by
    simpa [q] using hcount
  have hinv : Tendsto (fun n => 1 / (q n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp hqTop)
  have herror : Tendsto error atTop (nhds 0) :=
    squeeze_zero' herrorNonneg herrorBound hinv
  have heq : (fun n =>
      (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ)) =ᶠ[atTop] fun n => 1 + error n := by
    filter_upwards [hrefPos] with n hn
    have hshort : balancedBlockShortLength (total n) (referenceLength n) =
        referenceLength n + extra n := by
      rfl
    rw [hshort]
    dsimp [error]
    rw [Nat.cast_add]
    field_simp [show (referenceLength n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  have hsum : Tendsto (fun n => (1 : ℝ) + error n) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add herror
  exact hsum.congr' heq.symm

/-- The longer balanced length is also asymptotic to the reference length. -/
theorem tendsto_balancedBlockLongLength_div_referenceLength
    {total referenceLength : ℕ → ℕ}
    (href : Tendsto (fun n => (referenceLength n : ℝ)) atTop atTop)
    (hcount : Tendsto
      (fun n => (balancedBlockCount (total n) (referenceLength n) : ℝ))
      atTop atTop) :
    Tendsto
      (fun n => ((balancedBlockShortLength (total n) (referenceLength n) + 1 : ℕ) : ℝ) /
        (referenceLength n : ℝ)) atTop (nhds 1) := by
  have hshort := tendsto_balancedBlockShortLength_div_referenceLength href hcount
  have hrefInv : Tendsto (fun n => (referenceLength n : ℝ)⁻¹)
      atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp href
  have hsum : Tendsto
      (fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ) + (referenceLength n : ℝ)⁻¹)
      atTop (nhds 1) := by
    simpa using hshort.add hrefInv
  have heq : (fun n =>
      ((balancedBlockShortLength (total n) (referenceLength n) + 1 : ℕ) : ℝ) /
        (referenceLength n : ℝ)) =ᶠ[atTop]
      fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ) + (referenceLength n : ℝ)⁻¹ := by
    filter_upwards [] with n
    rw [Nat.cast_add, Nat.cast_one]
    ring
  exact hsum.congr' heq.symm

/-! ## Counts of complete blocks -/

/-- The largest number of complete blocks of the given length that fit in a
horizon of `n` steps. -/
@[expose] noncomputable def blockCount (blockLength : ℕ → ℕ) (n : ℕ) : ℕ :=
  n / blockLength n

/-- Complete blocks fit in the available horizon. -/
theorem blockCount_mul_blockLength_le (blockLength : ℕ → ℕ) (n : ℕ) :
    blockCount blockLength n * blockLength n ≤ n :=
  Nat.div_mul_le_self n _

/-- When a block has positive length, the number of complete blocks brackets
the horizon: one more block would be too long. -/
theorem blockCount_mul_blockLength_le_lt_succ (blockLength : ℕ → ℕ) (n : ℕ)
    (hpos : 0 < blockLength n) :
    blockCount blockLength n * blockLength n ≤ n ∧
      n < (blockCount blockLength n + 1) * blockLength n := by
  refine ⟨blockCount_mul_blockLength_le blockLength n, ?_⟩
  have hdecomp : blockLength n * blockCount blockLength n +
      n % blockLength n = n := by
    rw [blockCount]
    exact Nat.div_add_mod n _
  have hr := Nat.mod_lt n hpos
  nlinarith [hdecomp, hr]

/-- The complete blocks cover all but less than one block length. -/
theorem sub_blockLength_lt_blockCount_mul_blockLength
    (blockLength : ℕ → ℕ) (n : ℕ) (hpos : 0 < blockLength n) :
    (n : ℝ) - blockLength n <
      (blockCount blockLength n : ℝ) * blockLength n := by
  have h := (blockCount_mul_blockLength_le_lt_succ blockLength n hpos).2
  have hcast : (n : ℝ) <
      ((blockCount blockLength n : ℝ) + 1) * blockLength n := by
    exact_mod_cast h
  nlinarith [hcast]

/-- The relative error in the number of covered steps is at most one block
length divided by the horizon. -/
theorem blockCount_mul_blockLength_div_sub_one_abs_le
    (blockLength : ℕ → ℕ) (n : ℕ)
    (hpos : 0 < blockLength n) (hn : 0 < n) :
    |((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n - 1| ≤
      (blockLength n : ℝ) / n := by
  set c : ℕ := blockCount blockLength n with hc
  set l : ℕ := blockLength n with hl
  have hbr := blockCount_mul_blockLength_le_lt_succ blockLength n hpos
  have hle : ((c * l : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbr.1
  have hlt : (n : ℝ) < (((c + 1) * l : ℕ) : ℝ) := by exact_mod_cast hbr.2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlen : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hpos
  have hcast : (((c + 1) * l : ℕ) : ℝ) = ((c * l : ℕ) : ℝ) + (l : ℝ) := by
    have : (c + 1) * l = c * l + l := by ring
    rw [this]
    push_cast
    ring
  have hkey : (n : ℝ) - (l : ℝ) < ((c * l : ℕ) : ℝ) := by linarith [hlt, hcast]
  have h1 : ((c * l : ℕ) : ℝ) - (n : ℝ) ≤ 0 := by linarith
  have h2 : -(((c * l : ℕ) : ℝ) - (n : ℝ)) ≤ (l : ℝ) := by linarith
  have habs : |((c * l : ℕ) : ℝ) - (n : ℝ)| ≤ (l : ℝ) := by
    rw [abs_of_nonpos h1]
    exact h2
  rw [div_sub_one (ne_of_gt hnpos), abs_div, abs_of_pos hnpos]
  exact (div_le_div_iff_of_pos_right hnpos).mpr habs

/-- If the block length is `o(n)`, the number of covered steps is
asymptotic to the horizon. -/
theorem tendsto_blockCount_mul_blockLength_div_nat
    {blockLength : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hscale : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0)) :
    Tendsto (fun n => ((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n)
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop] at hscale ⊢
  intro ε hε
  rcases hscale ε hε with ⟨N₁, hN₁⟩
  rcases eventually_atTop.1 hpos with ⟨N₂, hN₂⟩
  refine ⟨max N₁ (max N₂ 1), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ (max N₂ 1)) hn
  have hN₂le : N₂ ≤ n :=
    le_trans (le_trans (le_max_left N₂ 1) (le_max_right N₁ (max N₂ 1))) hn
  have h1le : 1 ≤ n :=
    le_trans (le_trans (le_max_right N₂ 1) (le_max_right N₁ (max N₂ 1))) hn
  have hp : 0 < blockLength n := hN₂ n hN₂le
  have hn0 : 0 < n := h1le
  have hεn := hN₁ n hn1
  have hb := blockCount_mul_blockLength_div_sub_one_abs_le blockLength n hp hn0
  have hb' : |((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n - 1|
      ≤ |(blockLength n : ℝ) / n| := le_trans hb (le_abs_self _)
  rw [Real.dist_eq, sub_zero] at hεn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb' hεn

/-- Complete equal-length blocks occupy the same asymptotic fraction as an
arbitrary horizon sequence. This version is used for subintervals of a finite
partition, where the horizon is `⌊nt₁⌋ - ⌊nt₀⌋` rather than `n` itself. -/
theorem tendsto_quotientBlockCount_mul_blockLength_div_nat
    {horizon blockLength : ℕ → ℕ} {τ : ℝ}
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / n) atTop (nhds τ))
    (hblock : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0))
    (hpositive : ∀ᶠ n in atTop, 0 < blockLength n) :
    Tendsto (fun n =>
      ((horizon n / blockLength n * blockLength n : ℕ) : ℝ) / n)
      atTop (nhds τ) := by
  let covered : ℕ → ℝ := fun n =>
    ((horizon n / blockLength n * blockLength n : ℕ) : ℝ)
  have hlower : Tendsto (fun n => (horizon n : ℝ) / n -
      (blockLength n : ℝ) / n) atTop (nhds τ) := by
    simpa using hhorizon.sub hblock
  have hcovered : Tendsto (fun n => covered n / n) atTop (nhds τ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hhorizon
    · filter_upwards [hpositive, eventually_gt_atTop (0 : ℕ)] with n hlen hnNat
      have hdecomp : horizon n / blockLength n * blockLength n +
          horizon n % blockLength n = horizon n := by
        simpa [Nat.mul_comm] using Nat.div_add_mod (horizon n) (blockLength n)
      have hrem : horizon n % blockLength n < blockLength n :=
        Nat.mod_lt _ hlen
      have hgap :
          (horizon n : ℝ) - covered n < (blockLength n : ℝ) := by
        have hcast :
            covered n + (horizon n % blockLength n : ℝ) = horizon n := by
          dsimp [covered]
          exact_mod_cast hdecomp
        have hrem' : (horizon n % blockLength n : ℝ) < blockLength n :=
          by exact_mod_cast hrem
        rw [← hcast]
        linarith
      have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
      have hdiv := (div_lt_div_iff_of_pos_right hn).2 hgap
      rw [sub_div] at hdiv
      have hbound : (horizon n : ℝ) / n - (blockLength n : ℝ) / n <
          covered n / n := by
        linarith
      exact le_of_lt hbound
    · filter_upwards [hpositive, eventually_gt_atTop (0 : ℕ)] with n hlen hnNat
      have hle : horizon n / blockLength n * blockLength n ≤ horizon n :=
        Nat.div_mul_le_self _ _
      have hcast :
          ((horizon n / blockLength n * blockLength n : ℕ) : ℝ) ≤
            (horizon n : ℝ) := by
        exact_mod_cast hle
      have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
      exact (div_le_div_iff_of_pos_right hn).2 (by simpa [covered] using hcast)
  simpa [covered] using hcovered

end Asymptotics
