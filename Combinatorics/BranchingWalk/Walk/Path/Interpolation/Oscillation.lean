/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Block.Partition.Basic
public import Combinatorics.BranchingWalk.Walk.Path.Interpolation
public import Mathlib.Topology.UnitInterval

/-!
# Oscillation bounds for polygonal walk paths

This file contains deterministic bridges from equal-block displacement
bounds to local bounds for the discrete grid underlying polygonal
interpolation.
-/

open Set

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- If two ordered times are closer than `(length - 1) / n`, their grid
indices are separated by at most `length`.  The subtraction of one absorbs
the two floor errors. -/
theorem natFloor_mul_sub_le_of_dist_lt
    {n length : ℕ} (hn : 0 < n) {s t : unitInterval}
    (hst : s ≤ t)
    (hdist : dist s t < ((length : ℝ) - 1) / n) :
    ⌊(n : ℝ) * (t : ℝ)⌋₊ - ⌊(n : ℝ) * (s : ℝ)⌋₊ ≤ length := by
  let left := ⌊(n : ℝ) * (s : ℝ)⌋₊
  let right := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hstReal : (s : ℝ) ≤ (t : ℝ) := hst
  have hleftNonneg : 0 ≤ (n : ℝ) * (s : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) s.property.1
  have hrightNonneg : 0 ≤ (n : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) t.property.1
  have hleftLe : (left : ℝ) ≤ (n : ℝ) * (s : ℝ) :=
    Nat.floor_le hleftNonneg
  have hrightLe : (right : ℝ) ≤ (n : ℝ) * (t : ℝ) :=
    Nat.floor_le hrightNonneg
  have hleftLt : (n : ℝ) * (s : ℝ) < (left : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hgridLe : left ≤ right := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left hstReal (Nat.cast_nonneg n)
  have htime : (n : ℝ) * ((t : ℝ) - (s : ℝ)) < (length : ℝ) - 1 := by
    have hdistReal : (t : ℝ) - (s : ℝ) <
        ((length : ℝ) - 1) / n := by
      change |(s : ℝ) - (t : ℝ)| < ((length : ℝ) - 1) / n at hdist
      simpa [abs_of_nonpos (sub_nonpos.mpr hstReal)] using hdist
    simpa [mul_comm] using (lt_div_iff₀ hnReal).mp hdistReal
  have hcast : ((right - left : ℕ) : ℝ) < (length : ℝ) := by
    rw [Nat.cast_sub hgridLe]
    nlinarith
  exact (Nat.cast_lt).mp hcast |>.le

/-- Equal-block displacement bounds control the partial-sum difference at
two nearby ordered grid times. -/
theorem abs_partialSum_natFloor_mul_sub_le_three_mul
    {horizon blocks length n : ℕ} {radius : ℝ}
    {increment : ℕ → ℝ} (hn : 0 < n) (hlength : 0 < length)
    (hradius : 0 ≤ radius) (hcover : horizon ≤ blocks * length)
    {s t : unitInterval} (hst : s ≤ t)
    (hleft : ⌊(n : ℝ) * (s : ℝ)⌋₊ < horizon)
    (hright : ⌊(n : ℝ) * (t : ℝ)⌋₊ < horizon)
    (hdist : dist s t < ((length : ℝ) - 1) / n)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ radius) :
    |partialSum ⌊(n : ℝ) * (t : ℝ)⌋₊ increment -
        partialSum ⌊(n : ℝ) * (s : ℝ)⌋₊ increment| ≤ 3 * radius := by
  apply abs_partialSum_sub_le_three_mul_of_blockBounds
    hlength hradius hcover hleft hright
  · exact Nat.floor_mono <|
      mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n)
  · exact natFloor_mul_sub_le_of_dist_lt hn hst hdist
  · exact hblocks

/-- The preceding grid estimate in normalized step-path coordinates. -/
theorem abs_normalizedStepPath_sub_le_three_mul_div
    {horizon blocks length n : ℕ} {radius : ℝ} {scale : ℕ → ℝ}
    {increment : ℕ → ℝ} (hn : 0 < n) (hlength : 0 < length)
    (hradius : 0 ≤ radius) (hscale : 0 < scale n)
    (hcover : horizon ≤ blocks * length)
    {s t : unitInterval} (hst : s ≤ t)
    (hleft : ⌊(n : ℝ) * (s : ℝ)⌋₊ < horizon)
    (hright : ⌊(n : ℝ) * (t : ℝ)⌋₊ < horizon)
    (hdist : dist s t < ((length : ℝ) - 1) / n)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ radius) :
    |normalizedStepPath scale n increment t -
        normalizedStepPath scale n increment s| ≤ 3 * radius / scale n := by
  have hsum := abs_partialSum_natFloor_mul_sub_le_three_mul
    hn hlength hradius hcover hst hleft hright hdist hblocks
  unfold normalizedStepPath
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hscale)]
  calc
    (scale n)⁻¹ *
        |partialSum ⌊(n : ℝ) * (t : ℝ)⌋₊ increment -
          partialSum ⌊(n : ℝ) * (s : ℝ)⌋₊ increment| ≤
        (scale n)⁻¹ * (3 * radius) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hscale.le)
    _ = 3 * radius / scale n := by field_simp

/-- Under global block bounds, polygonal interpolation differs from its
right-continuous grid path by at most three normalized radii.  At time one
the two paths agree exactly, so no unused increment after the horizon is
required. -/
theorem abs_normalizedLinearPath_sub_normalizedStepPath_le_three_mul_div
    {blocks length n : ℕ} {radius : ℝ} {scale : ℕ → ℝ}
    {increment : ℕ → ℝ} (hn : 0 < n) (hlength : 0 < length)
    (hradius : 0 ≤ radius) (hscale : 0 < scale n)
    (hcover : n + 1 ≤ blocks * length)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ radius)
    (t : unitInterval) :
    |normalizedLinearPath scale n increment t -
        normalizedStepPath scale n increment t| ≤ 3 * radius / scale n := by
  let index := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hindexLe : index ≤ n := by
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
      _ = n := by ring
  by_cases hindex : index < n
  · have hincrement : |increment index| ≤ 3 * radius := by
      have hsum := abs_partialSum_sub_le_three_mul_of_blockBounds
        hlength hradius hcover
        (show index < n + 1 by omega)
        (show index + 1 < n + 1 by omega)
        (Nat.le_succ index)
        (show index + 1 - index ≤ length by omega)
        hblocks
      rw [partialSum_succ, add_sub_cancel_left] at hsum
      exact hsum
    calc
      |normalizedLinearPath scale n increment t -
          normalizedStepPath scale n increment t| ≤
          |(scale n)⁻¹| * |increment index| :=
        abs_normalizedLinearPath_sub_normalizedStepPath_le
          scale increment t
      _ ≤ (scale n)⁻¹ * (3 * radius) := by
        rw [abs_of_pos (inv_pos.mpr hscale)]
        exact mul_le_mul_of_nonneg_left hincrement
          (inv_nonneg.mpr hscale.le)
      _ = 3 * radius / scale n := by field_simp
  · have hindexEq : index = n := Nat.le_antisymm hindexLe
      (Nat.le_of_not_gt hindex)
    have hfloorLe : (index : ℝ) ≤ (n : ℝ) * (t : ℝ) :=
      Nat.floor_le <| mul_nonneg (Nat.cast_nonneg n) t.property.1
    have ht : (t : ℝ) = 1 := by
      rw [hindexEq] at hfloorLe
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      nlinarith [t.property.2]
    have hnonneg : 0 ≤ 3 * radius / scale n :=
      div_nonneg (mul_nonneg (by norm_num) hradius) hscale.le
    simpa [ht, normalizedStepPath] using hnonneg

/-- Equal-block displacement bounds give a deterministic modulus estimate
for the normalized polygonal path. -/
theorem abs_normalizedLinearPath_sub_le_nine_mul_div
    {blocks length n : ℕ} {radius : ℝ} {scale : ℕ → ℝ}
    {increment : ℕ → ℝ} (hn : 0 < n) (hlength : 0 < length)
    (hradius : 0 ≤ radius) (hscale : 0 < scale n)
    (hcover : n + 1 ≤ blocks * length)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ radius)
    {s t : unitInterval}
    (hdist : dist s t < ((length : ℝ) - 1) / n) :
    |normalizedLinearPath scale n increment t -
        normalizedLinearPath scale n increment s| ≤ 9 * radius / scale n := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm]
    exact this (s := t) (t := s)
      (by simpa [dist_comm] using hdist) (le_of_not_ge hst)
  have hleft : ⌊(n : ℝ) * (s : ℝ)⌋₊ < n + 1 := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) * (s : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left s.property.2 (Nat.cast_nonneg n)
      _ = n := by ring
  have hright : ⌊(n : ℝ) * (t : ℝ)⌋₊ < n + 1 := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
      _ = n := by ring
  have hlinearT :=
    abs_normalizedLinearPath_sub_normalizedStepPath_le_three_mul_div
      hn hlength hradius hscale hcover hblocks t
  have hlinearS :=
    abs_normalizedLinearPath_sub_normalizedStepPath_le_three_mul_div
      hn hlength hradius hscale hcover hblocks s
  have hstep := abs_normalizedStepPath_sub_le_three_mul_div
    hn hlength hradius hscale hcover hst hleft hright hdist hblocks
  have htriangleFirst := abs_sub_le
    (normalizedLinearPath scale n increment t)
    (normalizedStepPath scale n increment t)
    (normalizedLinearPath scale n increment s)
  have htriangleSecond := abs_sub_le
    (normalizedStepPath scale n increment t)
    (normalizedStepPath scale n increment s)
    (normalizedLinearPath scale n increment s)
  calc
    |normalizedLinearPath scale n increment t -
        normalizedLinearPath scale n increment s| ≤
        |normalizedLinearPath scale n increment t -
          normalizedStepPath scale n increment t| +
        |normalizedStepPath scale n increment t -
          normalizedStepPath scale n increment s| +
        |normalizedStepPath scale n increment s -
          normalizedLinearPath scale n increment s| := by
      calc
        |_ - _| ≤ |normalizedLinearPath scale n increment t -
              normalizedStepPath scale n increment t| +
            |normalizedStepPath scale n increment t -
              normalizedLinearPath scale n increment s| := htriangleFirst
        _ ≤ |normalizedLinearPath scale n increment t -
              normalizedStepPath scale n increment t| +
            (|normalizedStepPath scale n increment t -
              normalizedStepPath scale n increment s| +
            |normalizedStepPath scale n increment s -
              normalizedLinearPath scale n increment s|) :=
          add_le_add le_rfl htriangleSecond
        _ = _ := by ring
    _ ≤ (3 * radius / scale n) + (3 * radius / scale n) +
        (3 * radius / scale n) := by
      exact add_le_add (add_le_add hlinearT hstep) (by
        simpa [abs_sub_comm] using hlinearS)
    _ = 9 * radius / scale n := by ring

/-- The complement of the finite multiblock large-displacement event gives
a modulus bound for the polygonal path. -/
theorem dist_normalizedLinearContinuousPathIcc_le_of_not_exists_block
    {blocks length n : ℕ} {threshold : ℝ} {scale : ℕ → ℝ}
    {increment : ℕ → ℝ} (hn : 0 < n) (hlength : 0 < length)
    (hthreshold : 0 ≤ threshold) (hscale : 0 < scale n)
    (hcover : n + 1 ≤ blocks * length)
    (hgood : ¬∃ block < blocks,
      ∃ k ∈ Finset.range (length + 1),
        threshold * scale n ≤
          |blockSum (block * length) (k + 1) increment|) :
    ∀ {s t : unitInterval},
      dist s t < ((length : ℝ) - 1) / n →
      dist (normalizedLinearContinuousPathIcc scale n increment s)
        (normalizedLinearContinuousPathIcc scale n increment t) ≤
          9 * threshold := by
  have hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ threshold * scale n := by
    intro block hblock offset hoffset
    cases offset with
    | zero =>
        simpa using mul_nonneg hthreshold hscale.le
    | succ k =>
        have hk : k ∈ Finset.range (length + 1) := by
          simp
          omega
        exact le_of_not_ge fun hlarge =>
          hgood ⟨block, hblock, k, hk, hlarge⟩
  intro s t hdist
  have hpath := abs_normalizedLinearPath_sub_le_nine_mul_div
    hn hlength (mul_nonneg hthreshold hscale.le) hscale hcover hblocks hdist
  change |normalizedLinearPath scale n increment s -
      normalizedLinearPath scale n increment t| ≤ 9 * threshold
  rw [abs_sub_comm]
  calc
    |normalizedLinearPath scale n increment t -
        normalizedLinearPath scale n increment s| ≤
        9 * (threshold * scale n) / scale n := hpath
    _ = 9 * threshold := by field_simp

end Combinatorics.Branching.Walk
