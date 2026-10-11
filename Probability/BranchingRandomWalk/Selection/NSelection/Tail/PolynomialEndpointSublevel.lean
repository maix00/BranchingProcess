/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointSublevelSequence
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointDeviationParameters
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.LogarithmicScales

/-!
# Polynomial endpoint sublevel endpoint bounds at logarithmic scales

This module composes the finite-horizon branching estimate, the raw centered
spine range-rate estimate, and the polynomial conversion for the explicit
logarithmic scales.  The resulting theorem is an intermediate endpoint
estimate: its inputs include the centered finite-variance spine law and an
explicit range-rate margin.  The paper-level adapter deriving these inputs
from the flat offspring-law assumptions remains separate.  For a fixed raw
rate, `exists_endpoint_deviation_parameters` supplies `b` and a stricter margin by using
`C = targetRate * sigma ^ 2`; the caller must still provide the raw range-rate
and spatial-bin conditions.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- For the concrete logarithmic block scales, a raw centered-spine
range-rate estimate gives a polynomial endpoint bound.  The parameter `b`
is the drawdown ratio, and `hmargin` is the strict exponent margin after
including the spine variance.  The raw rate, bin condition, and moment law
are explicit so this declaration does not claim the still-open paper-level
derivation of those inputs. -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_logarithmicRawRate
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    {sigma : ℝ}
    (hspineMoment : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma)
    {m N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop)
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    {a b t zeta factor eta rangeRate targetRate : ℝ}
    (ha_one : a ≤ 1)
    (ht : 0 < t) (hb : 1 < b)
    (hfactor : 1 < factor) (heta : 0 < eta)
    (hrangeRate : 0 < rangeRate) (k : ℕ) (hk : 0 < k)
    (hrangeRate_lt : rangeRate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy)
    (htargetRate : 0 < targetRate)
    (hgap : targetRate < rangeRate /
      (logarithmicRateBeta factor eta) ^ 2)
    (hbin : (zeta / b + 1) / eta < 1 ∨
      ¬ ∃ j : ℕ, (zeta / b + 1) / eta = (j : ℝ))
    (hmPow : ∀ᶠ n : ℕ in atTop,
      (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hmargin : a + zeta <
      (targetRate * sigma ^ 2) * t / b ^ 2) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n)
          (logarithmicHorizon N t n) (horder n)
          (logarithmicEndpointThreshold N zeta n)) ≤
        ENNReal.ofReal
          (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let beta : ℝ := logarithmicRateBeta factor eta
  let length : ℕ → ℕ := fun n => logarithmicBlockLength N beta b n
  let blocks : ℕ → ℕ := fun n => logarithmicBlockCount N beta b t n
  let horizon : ℕ → ℕ := fun n => logarithmicHorizon N t n
  let delta : ℕ → ℝ := fun n => logarithmicDrawdown N beta b n
  let width : ℕ → ℝ := fun n => eta * delta n
  let threshold : ℕ → ℝ := fun n => logarithmicEndpointThreshold N zeta n
  have hbeta : 0 < beta := by
    dsimp [beta, logarithmicRateBeta]
    positivity
  obtain ⟨K, hK, hscale, hlength, hblocks, hblockCost, htotalCost,
      hcovered, hcomplete, hdeltaPositive, hthresholdFloor, hscaleBlock⟩ :=
    logarithmicRawRateParameters hN hfactor heta (by linarith : 0 < b) ht hbin
  have hwidth : ∀ᶠ n : ℕ in atTop, width n = eta * delta n := by
    filter_upwards [] with n
    rfl
  have hthresholdRaw : ∀ᶠ n : ℕ in atTop,
      ⌊(threshold n + delta n) / width n⌋₊ = K := by
    filter_upwards [hthresholdFloor] with n hn
    simpa [width, threshold, delta, beta, logarithmicRateBeta] using hn
  have hmN : ∀ᶠ n : ℕ in atTop, m n ≤ N n := by
    have hNlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ N n :=
      hN.eventually_ge_atTop 1
    filter_upwards [hmPow, hNlarge] with n hmn hNn
    have hNreal : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hNn
    have hpower : (N n : ℝ) ^ a ≤ (N n : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNreal ha_one
    exact_mod_cast hmn.trans hpower
  have hraw : ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n) (horizon n)
          (horder n) (threshold n)) ≤
      (N n : ℝ≥0∞) *
          (((horizon n : ℝ≥0∞) + 1) ^ 2 *
            ENNReal.ofReal (Real.exp (-delta n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp
              (-(targetRate * sigma ^ 2) *
                ((horizon n : ℝ) / delta n ^ 2)))) := by
    have hcomplete' : ∀ᶠ n : ℕ in atTop,
        blocks n * length n ≤ horizon n := by
      filter_upwards [] with n
      exact hcomplete n
    have hraw' :=
      eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_of_rangeRate
        μ hboundary hspineMoment hsigma hscale horder
        (m := m) (N := N) (horizon := horizon) (blocks := blocks)
        (length := length) (delta := delta) (width := width)
        (threshold := threshold) K k hfactor heta hrangeRate hk
        hrangeRate_lt htargetRate hlength hblocks hblockCost htotalCost
        hcovered hcomplete' hwidth hthresholdRaw hscaleBlock
        (by simpa [beta, logarithmicRateBeta] using hgap) hmN hdeltaPositive
    filter_upwards [hraw'] with n hn
    simpa [horizon, delta, threshold] using hn
  have hNcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNcast
  have hH : Tendsto
      (fun n => (horizon n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t) := by
    simpa [horizon, logarithmOfSampleSize] using
      logarithmicHorizon_div_logCube_tendsto hN ht
  have hB : Tendsto (fun n => delta n / Real.log (N n : ℝ))
      atTop (𝓝 b) := by
    simpa [delta, beta, logarithmOfSampleSize] using
      logarithmicDrawdown_div_log_tendsto hN hbeta (by linarith : 0 < b)
  have hthresholdScale : Tendsto
      (fun n => threshold n / Real.log (N n : ℝ)) atTop (𝓝 zeta) := by
    have hlogPositive : ∀ᶠ n : ℕ in atTop, 0 < Real.log (N n : ℝ) :=
      hlog.eventually_gt_atTop 0
    have heq : (fun n => threshold n / Real.log (N n : ℝ)) =ᶠ[atTop]
        fun _ => zeta := by
      filter_upwards [hlogPositive] with n hn
      simp [threshold, logarithmicEndpointThreshold,
        logarithmOfSampleSize, div_eq_mul_inv, hn.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hleft :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_rawRate
      μ horder hN hH hB hthresholdScale ht hb hmPow hmargin hraw
  simpa [horizon, threshold] using hleft

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
