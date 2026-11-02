/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

/-!
# Rounded block lengths and horizon ratios

## Public declarations

For `a : ℕ → ℝ`, `floorBlockLength a n = ⌊a n⌋₊`. The module proves its
basic divergence and ratio limits, fixed-shift and segment-length limits,
and generic horizon/block comparisons. In particular, if `aₙ → ∞`, then
`⌊aₙ⌋/aₙ → 1`; if `Hₙ/n → d > 0` and `rₙ/n → 0`, then
`Hₙ/⌊rₙ⌋ → ∞` when the reference block diverges, and
`(Hₙ-rₙ)/n → d`.

Public declarations: `floorBlockLength`, `tendsto_floorBlockLength_atTop`,
`eventually_floorBlockLength_pos`, `tendsto_floorBlockLength_div_argument`,
`tendsto_floorBlockLength_div_sq_of_tendsto_atTop`,
`tendsto_floorBlockLength_add_nat_div_of_argument_ratio`,
`tendsto_floorTime_div_nat`, `tendsto_floorSegmentLength_div_nat`,
`tendsto_floorSegmentLength_sub_one_div_nat`, `floorBlockLength_le`,
`tendsto_nat_div_atTop_of_cast_ratio`,
`tendsto_nat_div_floorBlockLength_atTop_of_horizonRatio`,
`tendsto_nat_div_atTop_of_positive_horizonRatio_of_zero_blockRatio`,
`eventually_block_le_horizon_of_positive_density`, and
`tendsto_nat_sub_div_nat_of_horizon_and_vanishingBlock`.

Writing `r_n=\lfloor a_n\rfloor`, the rounding and horizon consequences are
\[
  a_n\to\infty\quad\Longrightarrow\quad\frac{r_n}{a_n}\to1,
  \qquad
  a_n\to\infty,\ \frac{H_n}{a_n}\to\infty
    \quad\Longrightarrow\quad\frac{H_n}{r_n}\to\infty,
\]
and, when `H_n/n → d > 0` and `r_n/n → 0`,
\[
  \frac{H_n-r_n}{n}\longrightarrow d.
\]
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

/-- If a spatial scale diverges, rounding down a positive constant times its
square preserves that constant after division by the squared scale. -/
theorem tendsto_floorBlockLength_div_sq_of_tendsto_atTop
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
      (floorBlockLength (fun n => constant * scale n ^ 2) n : ℝ) /
        scale n ^ 2) atTop (nhds constant) := by
  have hsquare : Tendsto (fun n => scale n * scale n) atTop atTop :=
    hscale.atTop_mul_atTop₀ hscale
  have hargument : Tendsto (fun n => constant * scale n ^ 2) atTop atTop := by
    simpa [pow_two] using hsquare.const_mul_atTop hconstant
  have hratio := tendsto_floorBlockLength_div_argument hargument
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hmul := hratio.mul_const constant
  convert hmul.congr' ?_ using 1
  · norm_num
  · filter_upwards [hscalePos] with n hn
    dsimp [floorBlockLength]
    field_simp [hconstant.ne', hn.ne']

/-- Adding a fixed integer after rounding down does not alter an asymptotic
proportion. This packages the floor error for spatial grids whose real
argument is already known relative to a divergent denominator. -/
theorem tendsto_floorBlockLength_add_nat_div_of_argument_ratio
    {argument denominator : ℕ → ℝ} {limit : ℝ} (offset : ℕ)
    (hargument : Tendsto argument atTop atTop)
    (hdenominator : Tendsto denominator atTop atTop)
    (hratio : Tendsto (fun n => argument n / denominator n)
      atTop (nhds limit)) :
    Tendsto (fun n =>
      ((floorBlockLength argument n + offset : ℕ) : ℝ) / denominator n)
      atTop (nhds limit) := by
  have hproduct := (tendsto_floorBlockLength_div_argument hargument).mul hratio
  have heq : (fun n =>
      (floorBlockLength argument n : ℝ) / denominator n) =ᶠ[atTop]
      fun n =>
        ((floorBlockLength argument n : ℝ) / argument n) *
          (argument n / denominator n) := by
    filter_upwards [hargument.eventually_gt_atTop 0,
      hdenominator.eventually_gt_atTop 0] with n harg hden
    have hargNe : argument n ≠ 0 := ne_of_gt harg
    have hdenNe : denominator n ≠ 0 := ne_of_gt hden
    field_simp [hargNe, hdenNe]
  have hbase := hproduct.congr' heq.symm
  have hadd :
      (fun n =>
        ((floorBlockLength argument n + offset : ℕ) : ℝ) /
          denominator n) =ᶠ[atTop]
      fun n => (floorBlockLength argument n : ℝ) / denominator n +
        (offset : ℝ) / denominator n := by
    filter_upwards [] with n
    push_cast
    ring
  have hoffset : Tendsto (fun n => (offset : ℝ) / denominator n)
      atTop (nhds 0) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (offset : ℝ))
      atTop (nhds (offset : ℝ))).div_atTop hdenominator
  simpa using (hbase.add hoffset).congr' hadd.symm

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

/-- If the horizon dominates a positive divergent real block scale, then the
number of complete blocks obtained by rounding that scale down tends to
infinity. -/
theorem tendsto_nat_div_floorBlockLength_atTop_of_horizonRatio
    {horizon : ℕ → ℕ} {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop)
    (hratio : Tendsto (fun n => (horizon n : ℝ) / argument n)
      atTop atTop) :
    Tendsto (fun n => horizon n / floorBlockLength argument n)
      atTop atTop := by
  let length : ℕ → ℕ := floorBlockLength argument
  have hlengthTop : Tendsto length atTop atTop :=
    tendsto_floorBlockLength_atTop hargument
  have hlengthPos : ∀ᶠ n : ℕ in atTop, 0 < length n :=
    hlengthTop.eventually_gt_atTop 0
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      (horizon n : ℝ) / argument n ≤
        (horizon n : ℝ) / (length n : ℝ) := by
    filter_upwards [hargument.eventually_gt_atTop 0, hlengthPos] with
      n harg hlength
    have hlengthReal : 0 < (length n : ℝ) := by exact_mod_cast hlength
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlengthReal
      (floorBlockLength_le (le_of_lt harg))
  have hratioBlocks : Tendsto
      (fun n => (horizon n : ℝ) / (length n : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_mono' atTop hratioLower hratio
  exact tendsto_nat_div_atTop_of_cast_ratio hlengthPos hratioBlocks

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
end Asymptotics
