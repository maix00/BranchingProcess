/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseEndpointWindows
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BinParameters

/-!
# Uniform width and time conditions for the staircase blocks

The public theorem in this file is:

- `staircaseBlockNumericConditions`:
  from $\ell\le|I_j|<2\ell$ and
  $\Delta/2\le\Delta(j)\le\Delta$ and
  $\Delta(j)\ge\Delta-2c\ell/\Delta^2$, common conditions at
  $\beta\Delta/2$, $\beta\Delta$, and
  $\beta(\Delta-2c\ell/\Delta^2)$, where
  $\beta=1-1/(3m)$, give for every actual block the width threshold,
  inverse-margin bound, time-to-width ratio, and exponent comparison
  required by the staircase product.

These are the estimates following the two block-length bounds in Wang
Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5. Endpoint fractions for ordinary
and final blocks are treated separately in the product theorem.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Four numeric staircase requirements follow uniformly from one pair
of global width comparisons and the scheduled block-length bounds. -/
theorem staircaseBlockNumericConditions
    {entrance horizon blockLength m width₀ ratio₀ : ℕ}
    {globalWidth drift margin narrowedRate blockRate : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hm : 2 ≤ m)
    (hwidth : 0 < globalWidth) (hdrift : 0 ≤ drift)
    (hblockRate : 0 ≤ blockRate)
    (hcost : 4 * drift * (blockLength : ℝ) ≤ globalWidth ^ 3)
    (hfloorThreshold : width₀ ≤
      ⌊staircaseBinWidth m * (globalWidth / 2)⌋₊)
    (hmargin : 1 / margin ≤
      staircaseBinWidth m * (globalWidth / 2))
    (htime : ratio₀ *
      ⌊staircaseBinWidth m * globalWidth⌋₊ ^ 2 ≤ blockLength)
    (hrate : narrowedRate * globalWidth ^ 2 ≤
      blockRate *
        (⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ : ℝ) ^ 2)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    let actualWidth := staircaseTubeWidth globalWidth drift
      (staircaseBlockLength entrance horizon blockLength) j
    let narrowedWidth := staircaseBinWidth m * actualWidth
    width₀ ≤ ⌊narrowedWidth⌋₊ ∧
    1 / margin ≤ narrowedWidth ∧
    ratio₀ * ⌊narrowedWidth⌋₊ ^ 2 ≤
      staircaseBlockLength entrance horizon blockLength j ∧
    narrowedRate * globalWidth ^ 2 ≤
      blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 := by
  let actualWidth := staircaseTubeWidth globalWidth drift
    (staircaseBlockLength entrance horizon blockLength) j
  let narrowedWidth := staircaseBinWidth m * actualWidth
  have hhalf : globalWidth / 2 ≤ actualWidth :=
    staircaseTubeWidth_ge_half_of_schedule_bound hentrance
      hblockLength hwidth hdrift hcost hj
  have hfull : actualWidth ≤ globalWidth :=
    staircaseTubeWidth_le_globalWidth hdrift
  have hcommon :
      globalWidth - 2 * drift * (blockLength : ℝ) /
          globalWidth ^ 2 ≤ actualWidth :=
    staircaseTubeWidth_ge_commonLossBound hentrance
      hblockLength hwidth hdrift hj
  have hβ : 0 ≤ staircaseBinWidth m :=
    (staircaseBinWidth_pos hm).le
  have hlow : staircaseBinWidth m * (globalWidth / 2) ≤
      narrowedWidth :=
    mul_le_mul_of_nonneg_left hhalf hβ
  have hhigh : narrowedWidth ≤ staircaseBinWidth m * globalWidth :=
    mul_le_mul_of_nonneg_left hfull hβ
  have hfloorLow :
      ⌊staircaseBinWidth m * (globalWidth / 2)⌋₊ ≤
        ⌊narrowedWidth⌋₊ := Nat.floor_mono hlow
  have hfloorHigh : ⌊narrowedWidth⌋₊ ≤
      ⌊staircaseBinWidth m * globalWidth⌋₊ := Nat.floor_mono hhigh
  have hfloorRate :
      ⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ ≤ ⌊narrowedWidth⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hcommon hβ)
  have hlength := (staircaseBlockLength_bounds
    hentrance hblockLength hj).1
  have htime' : ratio₀ * ⌊narrowedWidth⌋₊ ^ 2 ≤
      staircaseBlockLength entrance horizon blockLength j := by
    have hsquare : ⌊narrowedWidth⌋₊ ^ 2 ≤
        ⌊staircaseBinWidth m * globalWidth⌋₊ ^ 2 := by
      exact pow_le_pow_left₀ (Nat.zero_le _) hfloorHigh _
    have hscaled := Nat.mul_le_mul_left ratio₀ hsquare
    exact (hscaled.trans htime).trans hlength
  have hrate' : narrowedRate * globalWidth ^ 2 ≤
      blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 := by
    have hfloorReal :
        (⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ : ℝ) ≤
          (⌊narrowedWidth⌋₊ : ℝ) := by exact_mod_cast hfloorRate
    have hsquare :
        (⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ : ℝ) ^ 2 ≤
          (⌊narrowedWidth⌋₊ : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfloorReal _
    exact hrate.trans (mul_le_mul_of_nonneg_left hsquare hblockRate)
  exact ⟨hfloorThreshold.trans hfloorLow, hmargin.trans hlow,
    htime', hrate'⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
