import Combinatorics.BranchingWalk.Walk.Path.Block.Partition
import Combinatorics.BranchingWalk.Walk.Path.Interpolation

/-!
# Oscillation bounds for polygonal walk paths

This file contains deterministic bridges from equal-block displacement
bounds to local bounds for the discrete grid underlying polygonal
interpolation.
-/

open Set

namespace Combinatorics.Branching.Walk

/-- If two ordered times are closer than `(length - 1) / n`, their grid
indices are separated by at most `length`.  The subtraction of one absorbs
the two floor errors. -/
theorem natFloor_mul_sub_le_of_dist_lt
    {n length : ℕ} (hn : 0 < n) {s t : Skorokhod.UnitInterval}
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
    {s t : Skorokhod.UnitInterval} (hst : s ≤ t)
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
    {s t : Skorokhod.UnitInterval} (hst : s ≤ t)
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

end Combinatorics.Branching.Walk
