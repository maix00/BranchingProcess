/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.PZInput
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.LowCount
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.PowerBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.IndexTwo

/-!
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_rightTailPositiveASpineCorridor_ge_exp_neg_log`:
  for every `ε > 0`, the corridor lower bound is eventually at least
  `exp (-ε * log (N n))` and at most the corresponding tilted-walk corridor
  probability.

# First-stage PZ proof lemmas

This auxiliary module supplies the finite-variance corridor estimate used by
the first-stage Paley--Zygmund argument.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.BranchingRandomWalk.Spine


private lemma tendsto_rightTailPositiveASpineScale_div_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {v : ℝ} :
    Tendsto (fun n => (v / 2) * logarithmicSmallDeviationScale
      (rightTailFirstStageCutoff N n) /
        logarithmOfSampleSize N n) atTop (𝓝 (v / 2)) := by
  have h := (tendsto_rightTailFirstStageCutoff_smallDeviationScale_div_log hN).const_mul
    (v / 2)
  have heq : (fun n => (v / 2) * logarithmicSmallDeviationScale
      (rightTailFirstStageCutoff N n) /
        logarithmOfSampleSize N n) =ᶠ[atTop]
      fun n => (v / 2) * (logarithmicSmallDeviationScale
        (rightTailFirstStageCutoff N n) /
          logarithmOfSampleSize N n) := by
    filter_upwards [] with n
    ring
  simpa only [mul_one] using h.congr' heq.symm

private lemma centeredMoment_integrable_square_of_sigma_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma) :
    Integrable (fun x : ℝ => x ^ 2) ν := by
  have hsecond : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hν.2]
    exact sq_pos_of_pos hsigma
  exact Integrable.of_integral_ne_zero (ne_of_gt hsecond)

/-- The block used in the stable bridge has quadratic order in `log N`.
Only the convergence of truncated second moments is used here. -/
private lemma eventually_rightTailPositiveAStableBlock_ge_log_sq
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma v amplitude : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (hv : 0 < v) (hamplitude : 0 < amplitude) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * logarithmOfSampleSize N n ^ 2 ≤
        (stableBlockLength 2 ν (amplitude ^ 2)
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n) : ℝ) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let ell : ℕ → ℕ := rightTailFirstStageCutoff N
  let scale : ℕ → ℝ := fun k => (v / 2) * logarithmicSmallDeviationScale k
  let c : ℝ := amplitude ^ 2 * (v / 4) ^ 2 / (4 * sigma ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hscaleRatio : Tendsto (fun n => scale (ell n) / L n)
      atTop (𝓝 (v / 2)) := by
    simpa [L, ell, scale] using tendsto_rightTailPositiveASpineScale_div_log hN
  have hell : Tendsto ell atTop atTop := by
    simpa [ell] using tendsto_rightTailFirstStageCutoff_atTop hN
  have hscale : Tendsto (fun n => scale (ell n)) atTop atTop := by
    have hprod := hL.atTop_mul_pos (by linarith : 0 < v / 2) hscaleRatio
    have heq : (fun n => L n * (scale (ell n) / L n)) =ᶠ[atTop]
        fun n => scale (ell n) := by
      filter_upwards [hL.eventually_gt_atTop 0] with n hLn
      field_simp
    exact hprod.congr' heq
  have hsquare := centeredMoment_integrable_square_of_sigma_pos hν hsigma
  have htruncated : Tendsto
      (fun n => ProbabilityTheory.truncatedSecondMoment ν (scale (ell n)))
      atTop (𝓝 (sigma ^ 2)) := by
    simpa only [Function.comp_def, hν.2] using
      (ProbabilityTheory.tendsto_truncatedSecondMoment ν hsquare).comp hscale
  have hmomentLimit : sigma ^ 2 < 2 * sigma ^ 2 := by
    nlinarith [sq_pos_of_pos hsigma]
  have htruncatedUpper : ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.truncatedSecondMoment ν (scale (ell n)) ≤ 2 * sigma ^ 2 :=
    (htruncated.eventually (Iio_mem_nhds hmomentLimit)).mono
      (fun _ h => h.le)
  have hscaleLower : ∀ᶠ n : ℕ in atTop,
      v / 4 ≤ scale (ell n) / L n :=
    (hscaleRatio.eventually
      (Ioi_mem_nhds (by linarith : v / 4 < v / 2))).mono
      (fun _ h => h.le)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hscaleMomentPos : ∀ᶠ n : ℕ in atTop,
      0 < ProbabilityTheory.truncatedSecondMoment ν (scale (ell n)) := by
    have hpos := eventually_truncatedSecondMoment_pos ν hsquare
      (by rw [hν.2]; exact sq_pos_of_pos hsigma)
    exact hscale.eventually hpos
  have hargumentLower : ∀ᶠ n : ℕ in atTop,
      2 * c * L n ^ 2 ≤ stableBlockArgument 2 ν (amplitude ^ 2)
        (scale ∘ ell) n := by
    filter_upwards [htruncatedUpper, hscaleLower, hLpos, hscaleMomentPos,
      hscale.eventually_gt_atTop 2] with n hmoment hscaleN hLn hmomentPos hscaleNpos
    have hscaleSq : (v / 4) ^ 2 * L n ^ 2 ≤ (scale (ell n)) ^ 2 := by
      have hprod := mul_le_mul_of_nonneg_right hscaleN hLn.le
      have hprodEq : scale (ell n) / L n * L n = scale (ell n) := by
        field_simp [ne_of_gt hLn]
      rw [hprodEq] at hprod
      have hvprod : 0 ≤ (v / 4) * L n := by positivity
      nlinarith [sq_nonneg (scale (ell n) - (v / 4) * L n)]
    have harg : stableBlockArgument 2 ν (amplitude ^ 2) (scale ∘ ell) n =
        amplitude ^ 2 * (scale (ell n)) ^ 2 /
          ProbabilityTheory.truncatedSecondMoment ν (scale (ell n)) := by
      rw [stableBlockArgument, stableSlowVariation_two]
      simp [Function.comp_apply]
    rw [harg]
    have hquot :
        amplitude ^ 2 * (v / 4) ^ 2 * L n ^ 2 /
            (2 * sigma ^ 2) ≤
          amplitude ^ 2 * (scale (ell n)) ^ 2 /
            ProbabilityTheory.truncatedSecondMoment ν (scale (ell n)) := by
      apply (div_le_div_iff₀ (by positivity) hmomentPos).2
      have hnum : amplitude ^ 2 * (v / 4) ^ 2 * L n ^ 2 ≤
          amplitude ^ 2 * (scale (ell n)) ^ 2 := by
        calc
          amplitude ^ 2 * (v / 4) ^ 2 * L n ^ 2 =
              amplitude ^ 2 * ((v / 4) ^ 2 * L n ^ 2) := by ring
          _ ≤ amplitude ^ 2 * (scale (ell n)) ^ 2 :=
            mul_le_mul_of_nonneg_left hscaleSq (sq_nonneg amplitude)
      exact mul_le_mul hnum hmoment (by positivity) (by positivity)
    have hcEq : 2 * c =
        amplitude ^ 2 * (v / 4) ^ 2 / (2 * sigma ^ 2) := by
      dsimp [c]
      ring
    rw [hcEq]
    convert hquot using 1; ring
  have hfloor : ∀ᶠ n : ℕ in atTop,
      c * L n ^ 2 ≤
        (stableBlockLength 2 ν (amplitude ^ 2) (scale ∘ ell) n : ℝ) := by
    have hLlarge : ∀ᶠ n : ℕ in atTop, 2 / c + 2 ≤ L n :=
      hL.eventually_ge_atTop (2 / c + 2)
    filter_upwards [hargumentLower, hLpos, hLlarge] with n harg hLn hLnLarge
    rw [stableBlockLength_two]
    have hargLarge : 2 ≤ stableBlockArgument 2 ν (amplitude ^ 2)
        (scale ∘ ell) n := by
      have hthresholdPos : 0 < 2 / c + 2 := by positivity
      have hthresholdSq : (2 / c + 2) ^ 2 ≤ L n ^ 2 := by
        nlinarith [sq_nonneg (L n - (2 / c + 2))]
      have hthreshold : 2 ≤ 2 * c * (2 / c + 2) ^ 2 := by
        have hcne : c ≠ 0 := hc.ne'
        field_simp [hcne]
        nlinarith [sq_nonneg (c - 1)]
      have hscaleLarge : 2 ≤ 2 * c * L n ^ 2 := by
        calc
          2 ≤ 2 * c * (2 / c + 2) ^ 2 := hthreshold
          _ ≤ 2 * c * L n ^ 2 := by
            exact mul_le_mul_of_nonneg_left hthresholdSq (by positivity)
      exact hscaleLarge.trans harg
    have hf := Nat.lt_floor_add_one
      (stableBlockArgument 2 ν (amplitude ^ 2) (scale ∘ ell) n)
    have hf' : stableBlockArgument 2 ν (amplitude ^ 2) (scale ∘ ell) n <
        ((stableBlockLength 2 ν (amplitude ^ 2) (scale ∘ ell) n : ℕ) : ℝ) + 1 := by
      simpa [stableBlockLength, stableBlockArgument] using hf
    dsimp [ell, scale] at harg ⊢
    have hfloorReal : stableBlockArgument 2 ν (amplitude ^ 2)
        (fun k => (v / 2) * logarithmicSmallDeviationScale k)
        (rightTailFirstStageCutoff N n) <
        (stableBlockLength 2 ν (amplitude ^ 2)
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n) : ℝ) + 1 := by
      simpa [stableBlockLength] using Nat.lt_floor_add_one
        (stableBlockArgument 2 ν (amplitude ^ 2)
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n))
    have hargLower : 2 * c * L n ^ 2 ≤ stableBlockArgument 2 ν
        (amplitude ^ 2) (fun k => (v / 2) * logarithmicSmallDeviationScale k)
        (rightTailFirstStageCutoff N n) := by
      simpa [ell, scale, Function.comp_apply, stableBlockArgument,
        stableSlowVariation_two] using harg
    have hthresholdSq : (2 / c + 2) ^ 2 ≤ L n ^ 2 := by
      have hthresholdNonneg : 0 ≤ 2 / c + 2 := by positivity
      have hprod : 0 ≤ (L n - (2 / c + 2)) * (L n + (2 / c + 2)) :=
        mul_nonneg (sub_nonneg.mpr hLnLarge) (by linarith)
      nlinarith [hprod]
    have hthreshold : 2 ≤ 2 * c * (2 / c + 2) ^ 2 := by
      have hcne : c ≠ 0 := hc.ne'
      field_simp [hcne]
      nlinarith [sq_nonneg (c - 1)]
    have hscaleLarge : 2 ≤ 2 * c * L n ^ 2 := by
      calc
        2 ≤ 2 * c * (2 / c + 2) ^ 2 := hthreshold
        _ ≤ 2 * c * L n ^ 2 :=
          mul_le_mul_of_nonneg_left hthresholdSq (by positivity)
    have hcL : 1 ≤ c * L n ^ 2 := by nlinarith [hscaleLarge]
    have htwice : c * L n ^ 2 ≤ 2 * c * L n ^ 2 - 1 := by
      nlinarith [hcL]
    have hfloorLower : c * L n ^ 2 ≤
        (stableBlockLength 2 ν (amplitude ^ 2)
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n) : ℝ) := by
      linarith [hargLower, hfloorReal, htwice]
    simpa [stableBlockLength, stableBlockArgument, stableSlowVariation_two] using hfloorLower
  exact ⟨c, hc, by simpa [L, ell, scale, Function.comp_apply] using hfloor⟩

private lemma tendsto_rightTailPositiveABridgeCount_div_log_zero
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma v amplitude : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (hv : 0 < v) (hamplitude : 0 < amplitude) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n =>
      ((Asymptotics.balancedBlockCount
        (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n) -
          stableBlockLength 2 ν (amplitude ^ 2)
            (fun k => (v / 2) * logarithmicSmallDeviationScale k)
            (rightTailFirstStageCutoff N n))
        (stableBlockLength 2 ν (amplitude ^ 2)
          (fun k => (v / 2) * logarithmicSmallDeviationScale k)
          (rightTailFirstStageCutoff N n)) : ℕ) : ℝ) /
        logarithmOfSampleSize N n) atTop (𝓝 0) := by
  obtain ⟨c, hc, hblock⟩ :=
    eventually_rightTailPositiveAStableBlock_ge_log_sq
      hN hν hsigma hv hamplitude
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let ell : ℕ → ℕ := rightTailFirstStageCutoff N
  let scale : ℕ → ℝ := fun k => (v / 2) * logarithmicSmallDeviationScale k
  let bridge : ℕ → ℕ := fun n =>
    ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength
      scale (ell n)
  let block : ℕ → ℕ := fun n => stableBlockLength 2 ν (amplitude ^ 2) scale (ell n)
  let count : ℕ → ℕ := fun n =>
    Asymptotics.balancedBlockCount (bridge n - block n) (block n)
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hellCube := tendsto_rightTailFirstStageCutoff_div_logCube hN
  have hupper : ∀ᶠ n : ℕ in atTop,
      (count n : ℝ) / L n ≤ ((ell n : ℝ) / L n ^ 3) / c := by
    filter_upwards [hblock, hLpos] with n hblockN hLn
    have hblockN' : c * L n ^ 2 ≤ (block n : ℝ) := by
      simpa [block, L, ell, scale] using hblockN
    have hblockPos : 0 < (block n : ℝ) := by
      have hpos : 0 < c * L n ^ 2 := mul_pos hc (sq_pos_of_pos hLn)
      exact lt_of_lt_of_le hpos hblockN'
    have hbridgeLe : bridge n ≤ ell n := by
      dsimp [bridge, ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength]
      exact Nat.sub_le _ _
    have hmainLe : bridge n - block n ≤ ell n := (Nat.sub_le _ _).trans hbridgeLe
    have hcountLe : (count n : ℝ) ≤
        (ell n : ℝ) / (block n : ℝ) := by
      calc
        (count n : ℝ) ≤ ((bridge n - block n : ℕ) : ℝ) / (block n : ℝ) := by
          dsimp [count, Asymptotics.balancedBlockCount]
          exact Nat.cast_div_le
        _ ≤ (ell n : ℝ) / (block n : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hmainLe)
            (Nat.cast_nonneg _)
    have hdenPos : 0 < c * L n ^ 2 := mul_pos hc (sq_pos_of_pos hLn)
    have hdiv : (ell n : ℝ) / (block n : ℝ) ≤
        (ell n : ℝ) / (c * L n ^ 2) := by
      apply (div_le_div_iff₀ hblockPos hdenPos).2
      have hellNonneg : (0 : ℝ) ≤ (ell n : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hellNonneg (sub_nonneg.mpr hblockN')]
    calc
      (count n : ℝ) / L n ≤
          ((ell n : ℝ) / (block n : ℝ)) / L n :=
        div_le_div_of_nonneg_right hcountLe hLn.le
      _ ≤ ((ell n : ℝ) / (c * L n ^ 2)) / L n :=
        div_le_div_of_nonneg_right hdiv hLn.le
      _ = ((ell n : ℝ) / L n ^ 3) / c := by
        field_simp [ne_of_gt hc, ne_of_gt hLn]
  have hrhs : Tendsto (fun n => ((ell n : ℝ) / L n ^ 3) / c)
      atTop (𝓝 0) := by
    simpa [L, ell] using (hellCube.div_const c)
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (count n : ℝ) / L n := by
    filter_upwards [hLpos] with n hLn
    exact div_nonneg (Nat.cast_nonneg _) hLn.le
  have hratio := squeeze_zero' hnonneg hupper hrhs
  exact ⟨c, hc, by simpa [count, bridge, block, scale, ell, L] using hratio⟩

private lemma eventually_rightTailPositiveAEntranceLength_le_log_sq
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v) :
    ∀ᶠ n : ℕ in atTop,
      (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
        (fun k => (v / 2) * logarithmicSmallDeviationScale k)
        (rightTailFirstStageCutoff N n) : ℝ) ≤
        v ^ 2 * logarithmOfSampleSize N n ^ 2 := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let ell : ℕ → ℕ := rightTailFirstStageCutoff N
  let scale : ℕ → ℝ := fun k => (v / 2) * logarithmicSmallDeviationScale k
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hratio : Tendsto (fun n => scale (ell n) / L n) atTop (𝓝 (v / 2)) := by
    simpa [L, ell, scale] using tendsto_rightTailPositiveASpineScale_div_log hN
  filter_upwards [hratio.eventually
      (Iio_mem_nhds (show v / 2 < v by linarith)),
    hratio.eventually (Ioi_mem_nhds (show v / 4 < v / 2 by linarith)),
    hL.eventually_gt_atTop 0] with n hnUpper hnLower hLn
  have hscaleLe : scale (ell n) ≤ v * L n := by
    have hmul := mul_lt_mul_of_pos_right hnUpper hLn
    have heq : scale (ell n) / L n * L n = scale (ell n) := by
      field_simp [ne_of_gt hLn]
    rw [heq] at hmul
    exact le_of_lt hmul
  have hscaleNonneg : 0 ≤ scale (ell n) := by
    have hratioPos : 0 < scale (ell n) / L n := by linarith
    have heq : scale (ell n) / L n * L n = scale (ell n) := by
      field_simp [ne_of_gt hLn]
    rw [← heq]
    exact le_of_lt (mul_pos hratioPos hLn)
  have hscaleSq : (scale (ell n)) ^ 2 ≤ (v * L n) ^ 2 := by
    have hprod : 0 ≤ (v * L n - scale (ell n)) *
        (v * L n + scale (ell n)) :=
      mul_nonneg (sub_nonneg.mpr hscaleLe) (by positivity)
    nlinarith [hprod]
  have hfloor :
      (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
        scale (ell n) : ℝ) ≤ (scale (ell n)) ^ 2 := by
    dsimp [ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength]
    exact Nat.floor_le (sq_nonneg (scale (ell n)))
  calc
    (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
        scale (ell n) : ℝ) ≤ (scale (ell n)) ^ 2 := hfloor
    _ ≤ (v * L n) ^ 2 := hscaleSq
    _ = v ^ 2 * L n ^ 2 := by ring

/-- Under the finite-variance hypothesis, the explicit first-stage
spine corridor estimate is at least `N ^ (-epsilon)` for every positive
epsilon, eventually. This turns the retained `exp(-O(sqrt(log N)))` bridge
factor into the polynomial-scale input required by the MRCA/PZ estimate. -/
lemma eventually_rightTailPositiveASpineCorridor_ge_exp_neg_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma b v epsilon : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) (hv : 0 < v) (hvb : v < b)
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, C < 0 ∧ ∃ entranceMass : ℝ≥0∞, 0 < entranceMass ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp (-epsilon * logarithmOfSampleSize N n)) ≤
          rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
            entranceMass (rightTailFirstStageCutoff N n) ∧
        rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
            entranceMass (rightTailFirstStageCutoff N n) ≤
          (tiltedIncrementFieldLaw realPotential μ)
            {increment : ℕ → ℝ |
              RandomWalk.history (rightTailFirstStageCutoff N n) 0
                increment ∈
                affineCorridorThrough (rightTailFirstStageCutoff N n)
                  (-b * logarithmOfSampleSize N n) 0
                  (b * logarithmOfSampleSize N n)
                  ((-b + v) * logarithmOfSampleSize N n)} := by
  obtain ⟨C, hC, entranceMass, hentranceMass, amplitude, hamplitude,
      hcorridor⟩ :=
    eventually_rightTailPositiveA_spineCorridor_lowerBound_of_centeredSecondMoment
      hN μ ν hν hνMoment hsigma hb hv hvb
  obtain ⟨c, hc, hcount⟩ :=
    tendsto_rightTailPositiveABridgeCount_div_log_zero
      hN hνMoment hsigma hv hamplitude
  have hEntrance := eventually_rightTailPositiveAEntranceLength_le_log_sq
    hN hv
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let ell : ℕ → ℕ := rightTailFirstStageCutoff N
  let scale : ℕ → ℝ := fun k => (v / 2) * logarithmicSmallDeviationScale k
  let entranceLength : ℕ → ℕ := fun n =>
    ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
      scale (ell n)
  let bridgeLength : ℕ → ℕ :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength
      scale ∘ ell
  let blockLength : ℕ → ℕ := fun n => stableBlockLength 2 ν
    (amplitude ^ 2) scale (ell n)
  let blockCount : ℕ → ℕ := fun n =>
    Asymptotics.balancedBlockCount (bridgeLength n - blockLength n)
      (blockLength n)
  let ratio : ℝ := (b - v / 4) / (v / 2)
  let exponent : ℝ :=
    (C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ 2
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hratio : 1 < ratio := by
    dsimp [ratio]
    rw [lt_div_iff₀ (by linarith : 0 < v / 2)]
    linarith
  have hratioDen : 0 < ratio / 2 - 13 / 60 := by linarith
  have hexponent : exponent < 0 := by
    dsimp [exponent]
    have hdiv : C / (ratio / 2 - 13 / 60) ^ (2 : ℝ) < 0 :=
      div_neg_of_neg_of_pos hC (Real.rpow_pos_of_pos hratioDen _)
    have hfactor : C / (ratio / 2 - 13 / 60) ^ (2 : ℝ) - 1 < 0 := by linarith
    exact mul_neg_of_neg_of_pos hfactor (sq_pos_of_pos hamplitude)
  let decayRate : ℝ := -exponent
  have hdecayRate : 0 < decayRate := by dsimp [decayRate]; linarith
  have hcountOne : Tendsto
      (fun n => ((blockCount n + 1 : ℕ) : ℝ) / L n) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := hL.inv_tendsto_atTop
    have hsum := hcount.add hinv
    have hsum' : Tendsto
        (fun n => (blockCount n : ℝ) / L n + (L n)⁻¹)
        atTop (𝓝 0) := by
      simpa [blockCount, bridgeLength, blockLength, scale, ell, L] using hsum
    have heq : (fun n => ((blockCount n + 1 : ℕ) : ℝ) / L n) =ᶠ[atTop]
        fun n => (blockCount n : ℝ) / L n + (L n)⁻¹ := by
      filter_upwards [] with n
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    exact hsum'.congr' heq.symm
  have hblockBudget : ∀ᶠ n : ℕ in atTop,
      decayRate * ((blockCount n + 1 : ℕ) : ℝ) ≤ epsilon / 2 * L n := by
    have hsmall := hcountOne.eventually
      (Iio_mem_nhds (show 0 < epsilon / (2 * decayRate) by positivity))
    filter_upwards [hsmall, hLpos] with n hn hLn
    have hmul := mul_lt_mul_of_pos_right hn hLn
    have hmul' := mul_lt_mul_of_pos_left hmul hdecayRate
    have hratioEq : decayRate *
        ((((blockCount n + 1 : ℕ) : ℝ) / L n) * L n) =
          decayRate * ((blockCount n + 1 : ℕ) : ℝ) := by
      field_simp [ne_of_gt hLn]
    rw [hratioEq] at hmul'
    have htargetEq : decayRate * (epsilon / (2 * decayRate) * L n) =
        epsilon / 2 * L n := by field_simp [ne_of_gt hdecayRate]
    rw [htargetEq] at hmul'
    exact le_of_lt hmul'
  have hcorridorEventually : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) ≤
        ENNReal.ofReal (Real.exp exponent) ^ (blockCount n + 1) := by
    filter_upwards [hblockBudget] with n hn
    have hexpArgument : -epsilon / 2 * L n ≤
        exponent * ((blockCount n + 1 : ℕ) : ℝ) := by
      dsimp [decayRate] at hn
      linarith
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg exponent) (blockCount n + 1)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_nat_mul]
    have hexpArgument' : -epsilon / 2 * L n ≤
        ((blockCount n + 1 : ℕ) : ℝ) * exponent := by
      simpa [mul_comm] using hexpArgument
    exact Real.exp_le_exp.mpr hexpArgument'
  have hq0 : (0 : ℝ≥0∞) < min entranceMass 1 := by
    exact lt_min hentranceMass (by norm_num)
  have hq0Top : min entranceMass 1 ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
  let entranceReal : ℝ := (min entranceMass 1).toReal
  have hentranceReal : 0 < entranceReal := by
    dsimp [entranceReal]
    exact ENNReal.toReal_pos hq0.ne' hq0Top
  have hquadraticDecay : Tendsto
      (fun x : ℝ => x ^ 2 * Real.exp (-(epsilon / 2) * x))
      atTop (𝓝 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      2 (epsilon / 2) (by linarith)
    have heq : (fun x : ℝ => x ^ 2 * Real.exp (-(epsilon / 2) * x)) =ᶠ[atTop]
        fun x => x ^ (2 : ℝ) * Real.exp (-(epsilon / 2) * x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp
    exact hraw.congr' heq.symm
  have hquadraticDecayL := hquadraticDecay.comp hL
  have hentranceBudget : ∀ᶠ n : ℕ in atTop,
      v ^ 2 * (L n ^ 2 * Real.exp (-(epsilon / 2) * L n)) < entranceReal := by
    have hzero : v ^ 2 * 0 < entranceReal := by simpa using hentranceReal
    have hsmall := (hquadraticDecayL.const_mul (v ^ 2)).eventually
      (Iio_mem_nhds hzero)
    filter_upwards [hsmall] with n hn
    simpa only [Function.comp_apply] using hn
  have hentranceEventually : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) ≤
        entranceMass / (entranceLength n : ℝ≥0∞) := by
    filter_upwards [hEntrance, hentranceBudget] with n hlen hbudget
    let epsMass : ℝ := Real.exp (-epsilon / 2 * L n)
    have hepsMass : 0 ≤ epsMass := Real.exp_nonneg _
    have hbudget' : v ^ 2 * (L n ^ 2 * epsMass) < entranceReal := by
      have hexpMass : epsMass = Real.exp (-(epsilon / 2) * L n) := by
        dsimp [epsMass]
        congr 1
        ring
      rw [hexpMass]
      exact hbudget
    have hmassReal : epsMass * (entranceLength n : ℝ) ≤ entranceReal := by
      calc
        epsMass * (entranceLength n : ℝ) ≤
            epsMass * (v ^ 2 * L n ^ 2) :=
          mul_le_mul_of_nonneg_left hlen hepsMass
        _ = v ^ 2 * (L n ^ 2 * epsMass) := by ring
        _ ≤ entranceReal := le_of_lt hbudget'
    have hmassENN : ENNReal.ofReal epsMass *
        (entranceLength n : ℝ≥0∞) ≤ min entranceMass 1 := by
      calc
        ENNReal.ofReal epsMass * (entranceLength n : ℝ≥0∞) =
            ENNReal.ofReal (epsMass * (entranceLength n : ℝ)) := by
              rw [← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul hepsMass]
        _ ≤ min entranceMass 1 := by
          rw [← ENNReal.ofReal_toReal hq0Top]
          exact ENNReal.ofReal_le_ofReal hmassReal
    have hdiv : ENNReal.ofReal epsMass ≤
        min entranceMass 1 / (entranceLength n : ℝ≥0∞) := by
      by_cases hzero : entranceLength n = 0
      · have hdenZero : (entranceLength n : ℝ≥0∞) = 0 := by simp [hzero]
        rw [hdenZero, ENNReal.div_zero (ne_of_gt hq0)]
        exact le_top
      · have hden0 : (entranceLength n : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast hzero
        have hdenTop : (entranceLength n : ℝ≥0∞) ≠ ∞ :=
          ENNReal.natCast_ne_top _
        exact (ENNReal.le_div_iff_mul_le (Or.inl hden0)
          (Or.inl hdenTop)).2 hmassENN
    calc
      ENNReal.ofReal epsMass ≤
          min entranceMass 1 / (entranceLength n : ℝ≥0∞) := hdiv
      _ ≤ entranceMass / (entranceLength n : ℝ≥0∞) :=
        ENNReal.div_le_div_right (min_le_left _ _) _
  refine ⟨C, hC, entranceMass, hentranceMass, amplitude, hamplitude, ?_⟩
  filter_upwards [hcorridorEventually, hentranceEventually, hcorridor]
    with n hbridge hentry hprob
  have hproduct :
      ENNReal.ofReal (Real.exp (-epsilon * L n)) ≤
        ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) *
          ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    exact le_of_eq (by ring)
  have hpower : ENNReal.ofReal (Real.exp (-epsilon * L n)) ≤
      rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
        entranceMass (rightTailFirstStageCutoff N n) := by
    calc
      ENNReal.ofReal (Real.exp (-epsilon * L n)) ≤
          ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) *
            ENNReal.ofReal (Real.exp (-epsilon / 2 * L n)) := hproduct
      _ ≤ ENNReal.ofReal (Real.exp exponent) ^ (blockCount n + 1) *
          (entranceMass / (entranceLength n : ℝ≥0∞)) :=
        mul_le_mul hbridge hentry (by positivity) (by positivity)
      _ = rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
          entranceMass (rightTailFirstStageCutoff N n) := by
        simp [rightTailPositiveASpineCorridorLowerBound, ell, scale,
          entranceLength, bridgeLength, blockLength, blockCount, ratio, exponent]
  exact ⟨by simpa [L] using hpower, hprob⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
