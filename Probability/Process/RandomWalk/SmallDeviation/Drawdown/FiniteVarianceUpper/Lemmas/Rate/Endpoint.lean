/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.Rate.Bounds
import Analysis.Asymptotics.Scale.IntermediatePowerBlock

/-!
# Endpoint and horizon powers for the drawdown estimate

The proof-specific declaration is
`ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers`:
for positive endpoint and horizon powers, centered increments with finite
positive variance, and $0<d<\pi^2\sigma^2/2$, sufficiently large widths and
horizons $L\ge\Delta^{2+\text{horizonPower}}$ satisfy
\[
  \mathbb P\!\left(B_{L,\Delta,\Delta/\text{endpointPower}}\right)
  \le \exp\!\left(-dL/\Delta^2\right).
\]

This assembles the rounded-maximum decomposition, fixed-pattern block
probabilities, and asymptotic block bounds in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.3.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- For positive endpoint and horizon powers, sufficiently large widths
give the finite-variance drawdown estimate. -/
lemma exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance endpointPower horizonPower d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    (hendpoint : 0 < endpointPower) (hhorizon : 0 < horizonPower)
    (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ horizon : ℕ,
        Delta ^ (2 + horizonPower) ≤ (horizon : ℝ) →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / endpointPower)) ≤
          Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
  obtain ⟨eta, hetaPos, hetaEndpoint, hetaHorizon, hetaOne, hcriticalEta⟩ :=
    exists_drawdownBlockExponent hvariance hendpoint hhorizon hd hcritical
  let B : ℝ := 1 + 2 * eta
  let blockRate : ℝ := d * B ^ 4
  let maxJumpFactor : ℝ := 2 * (1 / endpointPower + 2) / eta
  have hblockRatePos : 0 < blockRate := by
    dsimp [blockRate, B]
    positivity
  have hblockCritical : blockRate < (Real.pi ^ 2 / 2) * variance := by
    simpa [blockRate, B] using hcriticalEta
  obtain ⟨tubeWidth₀, htubeWidth₀, hblockBound⟩ :=
    iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance
      ν hν hsquare hvariance (by linarith : 0 < eta / 2)
      hblockRatePos hblockCritical
  have hscaleAbsorptions := eventually_drawdownScaleAbsorptions
    (endpointPower := endpointPower) (d := d) hetaHorizon hetaPos
  have hgood : ∀ᶠ Delta : ℝ in atTop,
      1 ≤ Delta ∧
      1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      Delta ^ (2 + eta / 2) ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta) ∧
      Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ B * Delta ∧
      (⌈eta * Delta⌉₊ + Delta) ^ (eta / 2) -
        blockRate * ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) /
          (⌈eta * Delta⌉₊ + Delta) ^ 2) ≤ -d * B * Delta ^ eta ∧
      2 * B * (1 / endpointPower + 2) / eta ^ 2 ≤
        Delta ^ (horizonPower - eta) ∧
      Real.log 2 / (d * eta) ≤ Delta ^ (eta / 2) ∧
      tubeWidth₀ ≤ Delta := by
    filter_upwards [Asymptotics.eventually_nat_floor_rpow_intermediate_bounds
        (p := 2 + eta / 2) (q := 2 + eta)
        (by linarith [hetaPos]) (by linarith [hetaPos]),
      eventually_drawdownCeilingBinWidth_bounds hetaPos,
      eventually_drawdownTubeBlockExponent_le hetaPos hd,
      hscaleAbsorptions, eventually_ge_atTop tubeWidth₀] with
      Delta hfloor hceil hexponent hscale hwidth₀
    refine ⟨hceil.1, hfloor.1, hfloor.2.2.1, hfloor.2.2.2,
      ?_, hexponent, ?_, hscale.2, hwidth₀⟩
    · simpa [B, add_comm] using hceil.2
    · simpa [B] using hscale.1
  obtain ⟨DeltaBound, hDeltaBound⟩ := Filter.eventually_atTop.1 hgood
  let Delta₀ := max 1 DeltaBound
  refine ⟨Delta₀, le_max_left _ _, ?_⟩
  intro Delta hDelta horizon hhorizon
  have hDeltaLarge : DeltaBound ≤ Delta :=
    (le_max_right _ _).trans hDelta
  obtain ⟨hDeltaOne, hlengthPos, hlengthLower, hlengthUpper, hwidthUpper,
    honeBlock, hjumpGrowth, hentropyGrowth, hwidth₀Le⟩ := hDeltaBound Delta hDeltaLarge
  have hDeltaPos : 0 < Delta := by linarith
  let blockLength : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  let binWidth : ℝ := (⌈eta * Delta⌉₊ : ℝ)
  let threshold : ℝ := Delta / endpointPower
  let q : ℕ := horizon / blockLength
  let K : ℕ := ⌊(threshold + Delta) / binWidth⌋₊ + 1
  let z : ℝ := (horizon : ℝ) / Delta ^ 2
  let t : ℝ := Delta ^ eta
  have hblockLength : 1 ≤ blockLength := by
    exact_mod_cast hlengthPos
  have hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ) := by
    exact hlengthLower
  have hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta) := by
    exact hlengthUpper
  have hpatternBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth' : ℝ, ∀ pattern : Finset (Fin q),
        (iidSequenceLaw ν).real
          (ProbabilityTheory.conditionalBlockIntersection
            (drawdownJumpPatternTubeEvent (horizon % blockLength) blockLength
              pattern upper binWidth' tubeWidth) q) ≤
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ (eta / 2) -
                blockRate * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
    intro tubeWidth hwidth upper binWidth' pattern
    exact measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound
      ν hblockBound (horizon % blockLength) q blockLength hblockLength
      tubeWidth hwidth upper binWidth' pattern
  have hbinWidthPos : 0 < binWidth := by
    dsimp [binWidth]
    exact lt_of_lt_of_le (mul_pos hetaPos hDeltaPos) (by exact_mod_cast Nat.le_ceil _)
  have hwidthThreshold : tubeWidth₀ ≤ binWidth + Delta := by
    dsimp [binWidth]
    have hbinNonneg : 0 ≤ (⌈eta * Delta⌉₊ : ℝ) := by positivity
    linarith
  have honeBlock' : (binWidth + Delta) ^ (eta / 2) -
      blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2) ≤
        -d * (1 + 2 * eta) * t := by
    simpa [binWidth, blockLength, t, B, add_comm] using honeBlock
  have hpowerHorizon : Delta ^ (2 + horizonPower) =
      Delta ^ 2 * Delta ^ horizonPower := by
    simpa [Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) horizonPower)
  have hzLower : Delta ^ horizonPower ≤ z := by
    apply (le_div_iff₀ (sq_pos_of_pos hDeltaPos)).2
    have h := hhorizon
    rw [hpowerHorizon] at h
    simpa [mul_comm] using h
  have hcounts := drawdownBlockCount_scaledBounds
    (horizon := horizon) (blockLength := blockLength) hDeltaPos
    hblockLength hblockLengthLower hblockLengthUpper
  have hqLower : z / t - 1 ≤ (q : ℝ) := by
    simpa [q, z, t] using hcounts.1
  have hqUpper : (q : ℝ) ≤ z / Real.sqrt t := by
    simpa [q, z, t] using hcounts.2
  have hpowerDifference : Delta ^ horizonPower =
      Delta ^ eta * Delta ^ (horizonPower - eta) := by
    calc
      Delta ^ horizonPower = Delta ^ (eta + (horizonPower - eta)) := by
        congr 1
        ring
      _ = Delta ^ eta * Delta ^ (horizonPower - eta) :=
        Real.rpow_add hDeltaPos eta (horizonPower - eta)
  have hratioGrowth : Delta ^ (horizonPower - eta) ≤ z / t := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hDeltaPos eta)).2
    calc
      Delta ^ (horizonPower - eta) * t = Delta ^ horizonPower := by
        rw [hpowerDifference]
        dsimp [t]
        ring
      _ ≤ z := hzLower
  have hconst : B * maxJumpFactor / eta ≤ Delta ^ (horizonPower - eta) := by
    calc
      B * maxJumpFactor / eta =
          2 * B * (1 / endpointPower + 2) / eta ^ 2 := by
            dsimp [maxJumpFactor]
            field_simp [ne_of_gt hetaPos]
      _ ≤ Delta ^ (horizonPower - eta) := by
        simpa [B] using hjumpGrowth
  have hjumpCountBound : (K : ℝ) + 1 ≤ maxJumpFactor := by
    dsimp [K, maxJumpFactor, threshold, binWidth]
    exact drawdownJumpCount_add_one_le hDeltaOne hendpoint hetaPos hetaOne.le
  have hKleq : K ≤ q := by
    have hfactor : 1 ≤ B / eta := by
      rw [one_le_div hetaPos]
      dsimp [B]
      linarith
    have hgrowth : maxJumpFactor ≤ Delta ^ (horizonPower - eta) := by
      calc
        maxJumpFactor = 1 * maxJumpFactor := by ring
        _ ≤ (B / eta) * maxJumpFactor :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = B * maxJumpFactor / eta := by ring
        _ ≤ Delta ^ (horizonPower - eta) := hconst
    have hKreal : (K : ℝ) ≤ (q : ℝ) := by
      nlinarith [hjumpCountBound, hqLower, hratioGrowth, hgrowth]
    exact_mod_cast hKreal
  have hmaxJumps : ⌊(threshold + Delta) / binWidth⌋₊ + 1 ≤ q := by
    simpa [K] using hKleq
  have hsqrt : Real.sqrt t = Delta ^ (eta / 2) := by
    dsimp [t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hDeltaPos.le]
    congr 1
    ring
  have hentropy : Real.log 2 / Real.sqrt t ≤ d * eta := by
    rw [hsqrt]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hDeltaPos (eta / 2))).2
    simpa [mul_comm] using
      (div_le_iff₀ (mul_pos hd hetaPos)).1 hentropyGrowth
  have hscaledJump : d * B * t * maxJumpFactor ≤ d * eta * Delta ^ horizonPower := by
    calc
      d * B * t * maxJumpFactor = (d * eta * t) *
          (B * maxJumpFactor / eta) := by
            dsimp [t]
            field_simp [ne_of_gt hetaPos]
      _ ≤ (d * eta * t) * Delta ^ (horizonPower - eta) :=
            mul_le_mul_of_nonneg_left hconst (by positivity)
      _ = d * eta * Delta ^ horizonPower := by
            rw [hpowerDifference]
            dsimp [t]
            ring
  have hjump : d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤ d * eta * z := by
    calc
      d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤
          d * B * t * maxJumpFactor := by
            exact mul_le_mul_of_nonneg_left hjumpCountBound (by positivity)
      _ ≤ d * eta * Delta ^ horizonPower := hscaledJump
      _ ≤ d * eta * z := mul_le_mul_of_nonneg_left hzLower (by positivity)
  have hsum := measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound
    ν horizon blockLength hpatternBound
    Delta threshold binWidth hbinWidthPos hwidthThreshold
  have hp : Real.exp ((binWidth + Delta) ^ (eta / 2) -
      blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hpositive : 0 < d * (1 + 2 * eta) * t := by positivity
    have hnonpos : -d * (1 + 2 * eta) * t ≤ 0 := by linarith
    exact honeBlock'.trans hnonpos
  have hfiniteBound := measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound
    ν horizon blockLength Delta threshold binWidth hsum hp
  have hsmallBlock :
      Real.exp ((binWidth + Delta) ^ (eta / 2) -
        blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ≤
      Real.exp (-d * (1 + 2 * eta) * t) := by
    apply Real.exp_le_exp.mpr
    exact honeBlock'
  have hpow :
      Real.exp ((binWidth + Delta) ^ (eta / 2) -
        blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ^ (q - K) ≤
      Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsmallBlock _
  have hfiniteBound' :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
        (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) := by
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
          (2 : ℝ) ^ q *
            Real.exp ((binWidth + Delta) ^ (eta / 2) -
              blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ^ (q - K) := by
                simpa [q, K, binWidth, threshold, blockLength] using hfiniteBound
      _ ≤ (2 : ℝ) ^ q *
          Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfinal := jumpPatternProbability_le_exp (by positivity) (by positivity)
    hetaPos hd hqLower hqUpper hKleq hentropy hjump
  have hprobability :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
        Real.exp (-d * z) := hfiniteBound'.trans hfinal
  simpa [threshold, z] using hprobability

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
