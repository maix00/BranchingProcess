/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale
public import Analysis.Asymptotics.BlockScale

/-!
# Diffusive block lengths

Mogulskii blocking uses integer time blocks whose length is asymptotic to a
positive constant times the square of the spatial scale.  This file isolates
the rounding facts from the probabilistic argument.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Asymptotics

/-- The integer block length obtained by rounding down a constant multiple of
the squared spatial scale. -/
noncomputable def diffusiveBlockLength
    (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊constant * scale n ^ 2⌋₊

/-- The real quantity rounded in `diffusiveBlockLength` diverges for every
positive block constant. -/
theorem IsMogulskiiScale.tendsto_const_mul_sq_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n => constant * scale n ^ 2) atTop atTop := by
  change IsSmallDeviationScale scale (fun n => Real.sqrt n) at hscale
  have hscaleAtTop : Tendsto scale atTop atTop :=
    IsSmallDeviationScale.tendsto_atTop hscale
  have hsquare : Tendsto (fun n => scale n * scale n) atTop atTop :=
    hscaleAtTop.atTop_mul_atTop₀ hscaleAtTop
  simpa [pow_two] using hsquare.const_mul_atTop hconstant

/-- Diffusive block lengths themselves tend to infinity. -/
theorem IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (diffusiveBlockLength constant scale) atTop atTop := by
  exact tendsto_floorBlockLength_atTop
    (hscale.tendsto_const_mul_sq_atTop hconstant)

/-- In particular, a diffusive block has positive integer length eventually. -/
theorem IsMogulskiiScale.eventually_diffusiveBlockLength_pos
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    ∀ᶠ n in atTop, 0 < diffusiveBlockLength constant scale n :=
  eventually_floorBlockLength_pos
    (hscale.tendsto_const_mul_sq_atTop hconstant)

/-- Rounding the diffusive block length has no effect after normalization by
the squared spatial scale. -/
theorem IsMogulskiiScale.tendsto_diffusiveBlockLength_div_sq
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        (diffusiveBlockLength constant scale n : ℝ) / scale n ^ 2)
      atTop (nhds constant) := by
  have hratio := tendsto_floorBlockLength_div_argument
    (hscale.tendsto_const_mul_sq_atTop hconstant)
  have hratio' : Tendsto (fun n =>
      (diffusiveBlockLength constant scale n : ℝ) /
        (constant * scale n ^ 2)) atTop (nhds 1) := by
    simpa [floorBlockLength, diffusiveBlockLength] using hratio
  have hmul := hratio'.mul_const constant
  convert hmul.congr' ?_ using 1
  · norm_num
  · filter_upwards [hscale.eventually_pos] with n hn
    dsimp [diffusiveBlockLength]
    field_simp [hconstant.ne', hn.ne']

/-- The square-root normalization of a diffusive block converges to the
square root of its block constant. -/
theorem IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        Real.sqrt (diffusiveBlockLength constant scale n) / scale n)
      atTop (nhds (Real.sqrt constant)) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (hscale.tendsto_diffusiveBlockLength_div_sq hconstant)
  apply hsqrt.congr'
  filter_upwards [hscale.eventually_pos] with n hn
  change Real.sqrt
      ((diffusiveBlockLength constant scale n : ℝ) / scale n ^ 2) = _
  rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq hn.le]

/-- The number of complete diffusive blocks available before time `n`
diverges. -/
theorem IsMogulskiiScale.tendsto_nat_div_diffusiveBlockLength_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n => n / diffusiveBlockLength constant scale n)
      atTop atTop := by
  rw [tendsto_atTop]
  intro blockCount
  have hratio : ∀ᶠ n : ℕ in atTop,
      (blockCount : ℝ) * constant ≤ (n : ℝ) / scale n ^ 2 :=
    hscale.tendsto_natCast_div_sq_atTop.eventually
      (eventually_ge_atTop ((blockCount : ℝ) * constant))
  filter_upwards [hratio, hscale.eventually_pos,
    hscale.eventually_diffusiveBlockLength_pos hconstant]
      with n hnRatio hnScale hnBlock
  apply (Nat.le_div_iff_mul_le hnBlock).2
  have hfloor :
      (diffusiveBlockLength constant scale n : ℝ) ≤
        constant * scale n ^ 2 := by
    exact Nat.floor_le (mul_nonneg hconstant.le (sq_nonneg _))
  have htime :
      ((blockCount * diffusiveBlockLength constant scale n : ℕ) : ℝ) ≤
        (n : ℝ) := by
    calc
      ((blockCount * diffusiveBlockLength constant scale n : ℕ) : ℝ) =
          (blockCount : ℝ) *
            (diffusiveBlockLength constant scale n : ℝ) := by norm_num
      _ ≤ (blockCount : ℝ) * (constant * scale n ^ 2) :=
        mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg blockCount)
      _ ≤ (n : ℝ) := by
        have hsquare : 0 < scale n ^ 2 := sq_pos_of_pos hnScale
        simpa [mul_assoc] using (le_div_iff₀ hsquare).mp hnRatio
  exact_mod_cast htime

/-- The complete-block exponent has the expected Mogulskii normalization.
The proof uses the Euclidean-division bounds, so the integer rounding errors
are handled here rather than in the probabilistic blocking argument. -/
theorem IsMogulskiiScale.tendsto_completeBlockCount_mul_sq_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
  have hblockRatio :=
    hscale.tendsto_diffusiveBlockLength_div_sq hconstant
  have hinverse : Tendsto (fun n =>
      scale n ^ 2 /
        (diffusiveBlockLength constant scale n : ℝ))
      atTop (nhds (1 / constant)) := by
    have hinv := hblockRatio.inv₀ hconstant.ne'
    convert hinv.congr' ?_ using 1 <;> simp [one_div]
  have hlower := hinverse.sub hscale.tendsto_sq_div_natCast_zero
  have hlower' : Tendsto (fun n =>
      scale n ^ 2 /
          (diffusiveBlockLength constant scale n : ℝ) -
        scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
    simpa using hlower
  apply hlower'.squeeze' hinverse
  · filter_upwards [hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant,
      eventually_gt_atTop 0] with n hnScale hnBlock hn
    have hdivision :
        n < (n / diffusiveBlockLength constant scale n + 1) *
          diffusiveBlockLength constant scale n := by
      simpa [mul_comm] using Nat.lt_mul_div_succ n hnBlock
    have hdivisionReal :
        (n : ℝ) <
          ((n / diffusiveBlockLength constant scale n + 1 : ℕ) : ℝ) *
            diffusiveBlockLength constant scale n := by
      exact_mod_cast hdivision
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hbReal : (0 : ℝ) < diffusiveBlockLength constant scale n := by
      exact_mod_cast hnBlock
    have hsquare : 0 ≤ scale n ^ 2 := sq_nonneg _
    push_cast at hdivisionReal
    have hquotient :
        (n : ℝ) / diffusiveBlockLength constant scale n ≤
          ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) + 1 :=
      (div_le_iff₀ hbReal).2 hdivisionReal.le
    have hmul := mul_le_mul_of_nonneg_right hquotient hsquare
    have hdiv := div_le_div_of_nonneg_right hmul hnReal.le
    rw [sub_le_iff_le_add]
    convert hdiv using 1
    all_goals field_simp [hnReal.ne', hbReal.ne']
  · filter_upwards [hscale.eventually_diffusiveBlockLength_pos hconstant,
      eventually_gt_atTop 0] with n hnBlock hn
    have hdivision := Nat.div_mul_le_self n
      (diffusiveBlockLength constant scale n)
    have hdivisionReal :
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
            diffusiveBlockLength constant scale n ≤ (n : ℝ) := by
      exact_mod_cast hdivision
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hbReal : (0 : ℝ) < diffusiveBlockLength constant scale n := by
      exact_mod_cast hnBlock
    have hsquare : 0 ≤ scale n ^ 2 := sq_nonneg _
    have hquotient :
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) ≤
          (n : ℝ) / diffusiveBlockLength constant scale n :=
      (le_div_iff₀ hbReal).2 hdivisionReal
    have hmul := mul_le_mul_of_nonneg_right hquotient hsquare
    have hdiv := div_le_div_of_nonneg_right hmul hnReal.le
    convert hdiv using 1
    all_goals field_simp [hnReal.ne', hbReal.ne']

/-- Counting one extra block for the incomplete tail has the same normalized
limit as counting only complete blocks. -/
theorem IsMogulskiiScale.tendsto_succ_completeBlockCount_mul_sq_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        ((n / diffusiveBlockLength constant scale n + 1 : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
  have hsum :=
    (hscale.tendsto_completeBlockCount_mul_sq_div hconstant).add
      hscale.tendsto_sq_div_natCast_zero
  have hsum' : Tendsto (fun n =>
      ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ) + scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [] with n
  push_cast
  ring

/-- Grouping a fixed positive number of diffusive blocks into one return
block divides the normalized number of complete blocks by that number.  The
extra block covering the final incomplete interval is asymptotically
negligible. -/
theorem IsMogulskiiScale.tendsto_succ_completeReturnBlockCount_mul_sq_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    Tendsto (fun n =>
        ((n / (blocks * diffusiveBlockLength constant scale n) + 1 : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / ((blocks : ℝ) * constant))) := by
  let ratio : ℕ → ℝ := fun n => scale n ^ 2 / (n : ℝ)
  let complete : ℕ → ℝ := fun n =>
    ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) * ratio n
  have hcomplete : Tendsto complete atTop (nhds (1 / constant)) := by
    convert hscale.tendsto_completeBlockCount_mul_sq_div hconstant using 1
    funext n
    dsimp [complete, ratio]
    ring
  have hlower : Tendsto (fun n => complete n / (blocks : ℝ)) atTop
      (nhds (1 / ((blocks : ℝ) * constant))) := by
    convert hcomplete.div_const (blocks : ℝ) using 1
    field_simp [show (blocks : ℝ) ≠ 0 by exact_mod_cast hblocks.ne']
  have hupper := hlower.add hscale.tendsto_sq_div_natCast_zero
  have hupper' : Tendsto
      (fun n => complete n / (blocks : ℝ) + scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / ((blocks : ℝ) * constant))) := by
    simpa using hupper
  apply hlower.squeeze' hupper'
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hblocksReal : (0 : ℝ) < blocks := by exact_mod_cast hblocks
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hratioNonneg : 0 ≤ ratio n := by
      exact div_nonneg (sq_nonneg _) hnReal.le
    let q := n / diffusiveBlockLength constant scale n
    have hq : q < blocks * (q / blocks + 1) :=
      Nat.lt_mul_div_succ q hblocks
    have hqReal : (q : ℝ) / blocks ≤ (q / blocks + 1 : ℕ) := by
      have hqCast : (q : ℝ) <
          (blocks : ℝ) * ((q / blocks + 1 : ℕ) : ℝ) := by
        exact_mod_cast hq
      exact ((div_lt_iff₀ hblocksReal).2 (by
        simpa [mul_comm] using hqCast)).le
    have hmul := mul_le_mul_of_nonneg_right hqReal hratioNonneg
    convert hmul using 1
    · dsimp [complete, ratio, q]
      ring
    · rw [show blocks * diffusiveBlockLength constant scale n =
          diffusiveBlockLength constant scale n * blocks from
            Nat.mul_comm _ _,
        ← Nat.div_div_eq_div_mul]
      dsimp [ratio, q]
      push_cast
      ring
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hblocksReal : (0 : ℝ) < blocks := by exact_mod_cast hblocks
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hratioNonneg : 0 ≤ ratio n := by
      exact div_nonneg (sq_nonneg _) hnReal.le
    let q := n / diffusiveBlockLength constant scale n
    have hq : q / blocks * blocks ≤ q := Nat.div_mul_le_self q blocks
    have hqReal : ((q / blocks : ℕ) : ℝ) ≤ (q : ℝ) / blocks := by
      apply (le_div_iff₀ hblocksReal).2
      exact_mod_cast hq
    have hmul := mul_le_mul_of_nonneg_right hqReal hratioNonneg
    have hadd := add_le_add_right hmul (ratio n)
    convert hadd using 1
    · rw [show blocks * diffusiveBlockLength constant scale n =
          diffusiveBlockLength constant scale n * blocks from
            Nat.mul_comm _ _,
        ← Nat.div_div_eq_div_mul]
      dsimp [ratio, q]
      push_cast
      ring
    · dsimp [complete, ratio, q]
      ring

end ProbabilityTheory.RandomWalk
