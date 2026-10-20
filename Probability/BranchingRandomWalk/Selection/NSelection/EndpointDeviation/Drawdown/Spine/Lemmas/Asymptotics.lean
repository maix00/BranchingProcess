/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.RandomWalkBounds

/-!
# Scale limits and Aïdékon--Hu asymptotics

This module contains non-reusable intermediate statements in the proof of
the positive-initial-mass capacity estimate, Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). The preceding module in the
`Lemmas/` chain supplies the definitions and estimates used here.

The declarations are theorem-specific reductions: they pass from the
restarted tube data to the estimates needed by the next stage of the proof.
Reusable path-event and measure inequalities remain in their semantic
modules outside this directory.

## Proof-chain statements

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_rightTailPositiveASecondStageAHScale` proves that $\Delta=cD^{1/3}$ eventually satisfies the Aïdékon--Hu width threshold and $\Delta^{2+p}\leq D$ for $p<1$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_atTop_of_cubicRatio`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_atTop_of_stageCubicRatios`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_atTop_of_logarithmicScales`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_root_div_log`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveA_log_add_one_div_log_of_cubic_scale`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveASpan_sublinearPower_div_log` establish divergence and logarithmic negligibility of the second-stage span.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.tendsto_rightTailPositiveAAHExponent_div_log_of_logarithmicScales` and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_rightTailPositiveAAHWeight_le_sampleSize_rpow` compare the Aïdékon--Hu exponent with $\log N$ and $N^{-p}$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_iidSequenceLaw_rightTailPositiveA_terminalDrawdown_le_ah`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_iidSequenceLaw_rightTailPositiveASecondStageTube_le_ah`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_iidSequenceLaw_rightTailPositiveASecondStageTube_le_ah_of_logarithmicScales` transfer the asymptotic rate to the terminal drawdown and full second-stage tube probabilities.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- If the planned second-stage span diverges, its spatial width eventually
passes the uniform Aïdékon--Hu scale threshold. For every `p < 1`, the full
span is also eventually longer than `width^(2+p)`. -/
theorem eventually_rightTailPositiveASecondStageAHScale
    (D : ℕ → ℕ) (c p delta0 : ℝ)
    (hc : 0 < c) (hp1 : p < 1)
    (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      delta0 ≤ c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) ∧
        (c * ((D n : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (D n : ℝ) := by
  have hwidth : Tendsto
      (fun n => c * ((D n : ℝ) ^ (3⁻¹ : ℝ))) atTop atTop := by
    exact ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3⁻¹ : ℝ))).comp hD)
      |>.const_mul_atTop hc
  have hexponent : 0 < (1 - p) / 3 := by linarith
  have hpower : Tendsto
      (fun n => (D n : ℝ) ^ ((1 - p) / 3)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hexponent).comp hD
  filter_upwards [hwidth.eventually_gt_atTop delta0,
    hpower.eventually_gt_atTop (c ^ (2 + p)),
    hD.eventually_gt_atTop 0] with n hwidthLarge hpowerLarge hDpos
  refine ⟨le_of_lt hwidthLarge, ?_⟩
  have hbase : 0 < (D n : ℝ) := hDpos
  have hwidthPow :
      (c * ((D n : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) =
        c ^ (2 + p) * (D n : ℝ) ^ ((2 + p) / 3) := by
    rw [Real.mul_rpow hc.le (by positivity)]
    rw [← Real.rpow_mul hbase.le]
    congr 1
    ring_nf
  have hmul := mul_lt_mul_of_pos_right hpowerLarge
    (Real.rpow_pos_of_pos hbase ((2 + p) / 3))
  have hproduct :
      (D n : ℝ) ^ ((1 - p) / 3) * (D n : ℝ) ^ ((2 + p) / 3) =
        (D n : ℝ) := by
    rw [← Real.rpow_add hbase]
    rw [show (1 - p) / 3 + (2 + p) / 3 = 1 by ring, Real.rpow_one]
  calc
    (c * ((D n : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) =
        c ^ (2 + p) * (D n : ℝ) ^ ((2 + p) / 3) := hwidthPow
    _ ≤ (D n : ℝ) ^ ((1 - p) / 3) * (D n : ℝ) ^ ((2 + p) / 3) :=
      le_of_lt (by nlinarith [hmul])
    _ = (D n : ℝ) := hproduct

/-- A positive cubic-scale limit forces the planned span itself to diverge. -/
theorem tendsto_rightTailPositiveASpan_atTop_of_cubicRatio
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t) :
    Tendsto (fun n => (D n : ℝ)) atTop atTop := by
  have hcube : Tendsto (fun n => L n ^ 3) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) |>.comp hL
  have hproduct := hcube.atTop_mul_pos ht hscale
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have heq : (fun n => L n ^ 3 * ((D n : ℝ) / L n ^ 3)) =ᶠ[atTop]
      fun n => (D n : ℝ) := by
    filter_upwards [hLpos] with n hn
    field_simp
  exact hproduct.congr' heq

/-- The cubic ratio of a two-stage span is the difference of the stage ratios,
provided the natural-valued cutoffs are eventually ordered. -/
theorem tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios
    {ell ellN : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hEll : Tendsto (fun n => (ell n : ℝ) / L n ^ 3) atTop (𝓝 0))
    (hEllN : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (hellN : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n) :
    Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have heq :
      (fun n => ((ellN n - ell n : ℕ) : ℝ) / L n ^ 3) =ᶠ[atTop]
        fun n => (ellN n : ℝ) / L n ^ 3 - (ell n : ℝ) / L n ^ 3 := by
    filter_upwards [hellN, hLpos] with n horder hLn
    rw [Nat.cast_sub horder]
    field_simp
  simpa using (hEllN.sub hEll).congr' heq.symm

/-- Cubic-scale limits for the two cutoffs imply divergence of their gap,
which is the scale hypothesis needed by the uniform terminal tube estimate. -/
theorem tendsto_rightTailPositiveASpan_atTop_of_stageCubicRatios
    {ell ellN : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hEll : Tendsto (fun n => (ell n : ℝ) / L n ^ 3) atTop (𝓝 0))
    (hEllN : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t)
    (hellN : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n) :
    Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_rightTailPositiveASpan_atTop_of_cubicRatio hL ?_ ht
  exact tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios
    hL hEll hEllN hellN

/-- The choices `ell = floor((log N)^(5/2))` and
`ellN = floor(t (log N)^3) + 1` have a diverging second-stage span. -/
theorem tendsto_rightTailPositiveASpan_atTop_of_logarithmicScales
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n =>
      ((logarithmicHorizon N t n - rightTailPositiveAFirstCutoff N n : ℕ) : ℝ))
      atTop atTop := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  apply tendsto_rightTailPositiveASpan_atTop_of_stageCubicRatios hL
    (by simpa [L] using tendsto_rightTailPositiveAFirstCutoff_div_logCube hN)
    (by simpa [L] using logarithmicHorizon_div_logCube_tendsto hN ht)
    ht
  exact (eventually_rightTailPositiveAFirstCutoff_lt_horizon hN ht).mono
    (fun _ h => Nat.le_of_lt h)

/-- A positive cubic-scale span has its cube-root width at the corresponding
linear logarithmic scale. -/
theorem tendsto_rightTailPositiveASpan_root_div_log
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t)) (ht : 0 < t) :
    Tendsto (fun n => (D n : ℝ) ^ (3⁻¹ : ℝ) / L n)
      atTop (𝓝 (t ^ (3⁻¹ : ℝ))) := by
  have hpow :=
    (Real.continuousAt_rpow_const t (3⁻¹ : ℝ)
      (Or.inl (ne_of_gt ht))).tendsto.comp hscale
  have heq : (fun n => (D n : ℝ) ^ (3⁻¹ : ℝ) / L n) =ᶠ[atTop]
      fun n => ((D n : ℝ) / L n ^ 3) ^ (3⁻¹ : ℝ) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hLn
    have hden : ((L n : ℝ) ^ 3) ^ (3⁻¹ : ℝ) = L n := by
      rw [← Real.rpow_natCast (L n) 3, ← Real.rpow_mul hLn.le]
      have hexp : (↑(3 : ℕ) : ℝ) * (3⁻¹ : ℝ) = 1 := by norm_num
      rw [hexp, Real.rpow_one]
    rw [Real.div_rpow (Nat.cast_nonneg (D n)) (by positivity) (3⁻¹ : ℝ), hden]
  exact hpow.congr' heq.symm

/-- A sequence with cubic logarithmic size has only a subexponential
logarithmic count: `log (u + 1) = o(log N)`. -/
theorem tendsto_rightTailPositiveA_log_add_one_div_log_of_cubic_scale
    {u L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hu : ∀ n, 0 ≤ u n)
    (hscale : Tendsto (fun n => u n / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t) :
    Tendsto (fun n => Real.log (u n + 1) / L n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop
  have hinvCube : Tendsto (fun n => (L n)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using hinv.pow 3
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hscaled : Tendsto (fun n => (u n + 1) / L n ^ 3)
      atTop (𝓝 t) := by
    have hsum := hscale.add hinvCube
    have heq : (fun n => (u n + 1) / L n ^ 3) =ᶠ[atTop]
        fun n => u n / L n ^ 3 + (L n)⁻¹ ^ 3 := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hlogScaled : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3)) atTop (𝓝 (Real.log t)) :=
    (Real.continuousAt_log (ne_of_gt ht)).tendsto.comp hscaled
  have hlogScaledDiv : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3) / L n)
      atTop (𝓝 0) := hlogScaled.div_atTop hL
  have hlogLDiv : Tendsto (fun n => Real.log (L n) / L n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp hL
    convert h using 1
    ext n
    simp [pow_one]
  have hsum := hlogScaledDiv.add (hlogLDiv.const_mul 3)
  have heq : (fun n => Real.log (u n + 1) / L n) =ᶠ[atTop]
      fun n => Real.log ((u n + 1) / L n ^ 3) / L n +
        3 * (Real.log (L n) / L n) := by
    filter_upwards [hLpos] with n hn
    have hu1 : 0 < u n + 1 := by linarith [hu n]
    rw [Real.log_div (ne_of_gt hu1) (pow_ne_zero 3 (ne_of_gt hn)),
      Real.log_pow]
    field_simp
    ring
  simpa using hsum.congr' heq.symm

/-- A sublinear power of the second-stage span is negligible compared with
`log N`. This is the `p < 1` remainder in the exponent of the long-prefix
Aïdékon--Hu terms. -/
theorem tendsto_rightTailPositiveASpan_sublinearPower_div_log
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t p : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t)) (ht : 0 < t)
    (hp1 : p < 1) :
    Tendsto (fun n => (D n : ℝ) ^ (p / 3) / L n)
      atTop (𝓝 0) := by
  let q : ℝ := p / 3
  have hratio :=
    (Real.continuousAt_rpow_const t q (Or.inl (ne_of_gt ht))).tendsto.comp hscale
  have hLp : Tendsto (fun n => L n ^ (p - 1)) atTop (𝓝 0) := by
    have hneg := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).comp hL
    convert hneg using 1
    ext n
    congr 1
    ring
  have hprod := hratio.mul hLp
  have heq : (fun n => (D n : ℝ) ^ q / L n) =ᶠ[atTop]
      fun n => ((D n : ℝ) / L n ^ 3) ^ q * L n ^ (p - 1) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hLn
    have hDnonneg : 0 ≤ (D n : ℝ) := Nat.cast_nonneg _
    have hratioNonneg : 0 ≤ (D n : ℝ) / L n ^ 3 :=
      div_nonneg hDnonneg (by positivity)
    let r : ℝ := (D n : ℝ) / L n ^ 3
    have hr : r = (D n : ℝ) / L n ^ 3 := rfl
    have hfactor : (D n : ℝ) ^ q = r ^ q * L n ^ p := by
      have hsplit : (D n : ℝ) =
          r * L n ^ 3 := by
        dsimp [r]
        field_simp [ne_of_gt hLn]
      calc
        (D n : ℝ) ^ q = (r * L n ^ 3) ^ q := by rw [hsplit]
        _ = r ^ q * (L n ^ 3) ^ q :=
          Real.mul_rpow (hratioNonneg.trans_eq hr) (by positivity)
        _ = r ^ q * L n ^ p := by
          rw [← Real.rpow_natCast (L n) 3, ← Real.rpow_mul hLn.le]
          have hexp : (↑(3 : ℕ) : ℝ) * q = p := by dsimp [q]; ring
          rw [hexp]
    calc
      (D n : ℝ) ^ q / L n =
          (r ^ q * L n ^ p) / L n := by rw [hfactor]
      _ = r ^ q * L n ^ (p - 1) := by
        calc
          (r ^ q * L n ^ p) / L n = r ^ q * (L n ^ p / L n) := by ring
          _ = r ^ q * L n ^ (p - 1) := by
            have hquot : L n ^ p / L n = L n ^ (p - 1) := by
              calc
                L n ^ p / L n = L n ^ p / L n ^ (1 : ℝ) :=
                  congrArg (fun x : ℝ => L n ^ p / x)
                    (Real.rpow_one (L n)).symm
                _ = L n ^ (p - 1) := (Real.rpow_sub hLn p 1).symm
            rw [hquot]
      _ = ((D n : ℝ) / L n ^ 3) ^ q * L n ^ (p - 1) := by rw [hr]
  simpa [q] using hprod.congr' heq.symm

/-- On the logarithmic scales, the exponent in the long-prefix
capacity contribution has the limiting rate `-b + v + c t^(1/3)`. The
additional `κ c^p L^(p/3)` term vanishes after division by `log N`. -/
theorem tendsto_rightTailPositiveAAHExponent_div_log_of_logarithmicScales
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t b v c κ p : ℝ}
    (ht : 0 < t) (hp1 : p < 1) :
    Tendsto
      (fun n => ((-b + v) * logarithmOfSampleSize N n +
          c * (((logarithmicHorizon N t n -
            rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
          κ * c ^ p * (((logarithmicHorizon N t n -
            rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) ^ (p / 3))) /
          logarithmOfSampleSize N n)
      atTop (𝓝 (-b + v + c * (t ^ (3⁻¹ : ℝ)))) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let D : ℕ → ℕ := fun n =>
    logarithmicHorizon N t n - rightTailPositiveAFirstCutoff N n
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hDscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    apply tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios hL
    · simpa [L] using tendsto_rightTailPositiveAFirstCutoff_div_logCube hN
    · simpa [L] using logarithmicHorizon_div_logCube_tendsto hN ht
    · exact (eventually_rightTailPositiveAFirstCutoff_lt_horizon hN ht).mono
        (fun _ h => Nat.le_of_lt h)
  have hroot := tendsto_rightTailPositiveASpan_root_div_log hL hDscale ht
  have hsmall := tendsto_rightTailPositiveASpan_sublinearPower_div_log
    hL hDscale ht hp1
  have hconstant : Tendsto (fun _ : ℕ => -b + v) atTop (𝓝 (-b + v)) :=
    tendsto_const_nhds
  have hrootTerm := hroot.const_mul c
  have hsmallTerm := hsmall.const_mul (κ * c ^ p)
  have hsum := (hconstant.add hrootTerm).add hsmallTerm
  have heq : (fun n =>
      ((-b + v) * L n + c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) +
        κ * c ^ p * ((D n : ℝ) ^ (p / 3))) / L n) =ᶠ[atTop]
      fun n => (-b + v) + c * ((D n : ℝ) ^ (3⁻¹ : ℝ) / L n) +
        κ * c ^ p * ((D n : ℝ) ^ (p / 3) / L n) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hLn
    field_simp [ne_of_gt hLn]
  have hlimit : Tendsto
      (fun n => (-b + v) + c * ((D n : ℝ) ^ (3⁻¹ : ℝ) / L n) +
        κ * c ^ p * ((D n : ℝ) ^ (p / 3) / L n))
      atTop (𝓝 (-b + v + c * (t ^ (3⁻¹ : ℝ)))) := by
    simpa using hsum
  simpa [L, D] using hlimit.congr' heq.symm

/-- Any rate strictly above the logarithmic limit controls the long-prefix
AH exponential weight by the corresponding power of the sample size. -/
theorem eventually_rightTailPositiveAAHWeight_le_sampleSize_rpow
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t b v c κ p rate : ℝ}
    (ht : 0 < t) (hp1 : p < 1)
    (hrate : -b + v + c * (t ^ (3⁻¹ : ℝ)) < rate) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp
        ((-b + v) * logarithmOfSampleSize N n +
          c * (((logarithmicHorizon N t n -
            rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
          κ * c ^ p * (((logarithmicHorizon N t n -
            rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) ^ (p / 3)))) ≤
        ENNReal.ofReal ((N n : ℝ) ^ rate) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let D : ℕ → ℕ := fun n =>
    logarithmicHorizon N t n - rightTailPositiveAFirstCutoff N n
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hlimit := tendsto_rightTailPositiveAAHExponent_div_log_of_logarithmicScales
    hN (t := t) (b := b) (v := v) (c := c) (κ := κ) (p := p) ht hp1
  have hrateEvent : ∀ᶠ n : ℕ in atTop,
      ((-b + v) * L n + c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) +
        κ * c ^ p * ((D n : ℝ) ^ (p / 3))) / L n < rate := by
    simpa [L, D] using
      (Filter.Tendsto.eventually hlimit (Iio_mem_nhds hrate))
  filter_upwards [hrateEvent, hL.eventually_gt_atTop 0,
    hN.eventually_gt_atTop 0] with n hn hLn hNn
  have hexponent :
      (-b + v) * L n + c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) +
        κ * c ^ p * ((D n : ℝ) ^ (p / 3)) < rate * L n := by
    exact (div_lt_iff₀ hLn).mp hn
  have hpow : (N n : ℝ) ^ rate = Real.exp (rate * L n) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hNn : (0 : ℝ) < (N n : ℝ))]
    simp [L, logarithmOfSampleSize, mul_comm]
  apply ENNReal.ofReal_le_ofReal
  rw [hpow]
  apply Real.exp_le_exp.mpr
  simpa [D] using le_of_lt hexponent

/-- Along any diverging planned span, the full terminal second-stage
drawdown probability obeys the uniform Aïdékon--Hu exponential estimate.
The restriction `p < 1` is exactly what makes `width^(2+p)` sublinear in the
planned span. -/
theorem eventually_iidSequenceLaw_rightTailPositiveA_terminalDrawdown_le_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (κ c target blockTarget p : ℝ)
    (hκ : 0 ≤ κ) (hc : 0 < c)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) (hp1 : p < 1)
    {ell ellN : ℕ → ℕ}
    (hellN : ∀ᶠ n : ℕ in atTop, ell n < ellN n)
    (hspan : Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          (ellN n - ell n)
          (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift (ell n) (ellN n) κ c (ellN n - ell n) +
            c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * ((ellN n - ell n : ℕ) : ℝ) /
            (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  let D : ℕ → ℕ := fun n => ellN n - ell n
  obtain ⟨delta0, _hdelta0, hAH⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
      ν hν hsigma hB hcontinuous hmeasurable κ c target blockTarget p
      hκ hc htarget htargetBlock hblockTarget hp
  have hscale := eventually_rightTailPositiveASecondStageAHScale
    D c p delta0 hc hp1 hspan
  filter_upwards [hscale, hellN] with n hscale horder
  have hbound := hAH (ell n) (ellN n) (D n) horder (by simp [D])
    (by simpa [D] using hscale.1) (by simpa [D] using hscale.2)
  simpa [D] using hbound

/-- The full second-stage tube has the same terminal Aïdékon--Hu bound,
because its affine corridor is contained in the associated drawdown event. -/
theorem eventually_iidSequenceLaw_rightTailPositiveASecondStageTube_le_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (κ c v target blockTarget p : ℝ)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) (hp1 : p < 1)
    {ell ellN : ℕ → ℕ}
    (hellN : ∀ᶠ n : ℕ in atTop, ell n < ellN n)
    (hspan : Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        (rightTailPositiveASecondStageTubeEvent (ell n) (ellN n) κ c v) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * ((ellN n - ell n : ℕ) : ℝ) /
            (c * (((ellN n - ell n : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  have hdrawdown := eventually_iidSequenceLaw_rightTailPositiveA_terminalDrawdown_le_ah
    ν hν hsigma hB hcontinuous hmeasurable κ c target blockTarget p hκ hc
    htarget htargetBlock hblockTarget hp hp1 hellN hspan
  filter_upwards [hdrawdown, hellN] with n hbound horder
  apply (measure_mono ?_).trans hbound
  exact rightTailPositiveASecondStageTubeEvent_subset_drawdownEvent
    (ell n) (ellN n) κ c v horder hκ hc hvc

/-- The logarithmic cutoff and terminal horizon satisfy the hypotheses
of the uniform second-stage tube estimate, so the full restarted tube inherits
the terminal Aïdékon--Hu bound eventually. -/
theorem eventually_iidSequenceLaw_rightTailPositiveASecondStageTube_le_ah_of_logarithmicScales
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (κ c v target blockTarget p : ℝ)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) (hp1 : p < 1)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        (rightTailPositiveASecondStageTubeEvent
          (rightTailPositiveAFirstCutoff N n) (logarithmicHorizon N t n)
          κ c v) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 *
            ((logarithmicHorizon N t n - rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) /
              (c * (((logarithmicHorizon N t n -
                rightTailPositiveAFirstCutoff N n : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  exact eventually_iidSequenceLaw_rightTailPositiveASecondStageTube_le_ah
    ν hν hsigma hB hcontinuous hmeasurable κ c v target blockTarget p hκ hc hvc
    htarget htargetBlock hblockTarget hp hp1
    (eventually_rightTailPositiveAFirstCutoff_lt_horizon hN ht)
    (tendsto_rightTailPositiveASpan_atTop_of_logarithmicScales hN ht)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
