/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Theorems
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound
import Analysis.Asymptotics.Sequence.LogarithmicScale

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.RandomWalkBounds
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

## Internal proof declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_positiveASecondStageAHScale` proves that $\Delta=cD^{1/3}$ eventually satisfies the Aïdékon--Hu width threshold and $\Delta^{2+p}\leq D$ for $p<1$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_atTop_of_cubicRatio`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_cubicRatio_of_stageRatios`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_atTop_of_stageCubicRatios`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_atTop_of_logarithmicScales`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_root_div_log`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveASpan_sublinearPower_div_log` establish divergence and the remaining logarithmic-scale asymptotics of the second-stage span.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_positiveAAHExponent_div_log_of_logarithmicScales` gives the logarithmic rate of the Aïdékon--Hu exponent.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- If the planned second-stage span diverges, its spatial width eventually
passes the uniform Aïdékon--Hu scale threshold. For every `p < 1`, the full
span is also eventually longer than `width^(2+p)`. -/
lemma eventually_positiveASecondStageAHScale
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
lemma tendsto_positiveASpan_atTop_of_cubicRatio
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
lemma tendsto_positiveASpan_cubicRatio_of_stageRatios
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
lemma tendsto_positiveASpan_atTop_of_stageCubicRatios
    {ell ellN : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hEll : Tendsto (fun n => (ell n : ℝ) / L n ^ 3) atTop (𝓝 0))
    (hEllN : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t)
    (hellN : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n) :
    Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_positiveASpan_atTop_of_cubicRatio hL ?_ ht
  exact tendsto_positiveASpan_cubicRatio_of_stageRatios
    hL hEll hEllN hellN

/-- The choices `ell = floor((log N)^(5/2))` and
`ellN = floor(t (log N)^3) + 1` have a diverging second-stage span. -/
lemma tendsto_positiveASpan_atTop_of_logarithmicScales
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n =>
      ((logarithmicHorizon N t n - positiveAFirstStageCutoff N n : ℕ) : ℝ))
      atTop atTop := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  apply tendsto_positiveASpan_atTop_of_stageCubicRatios hL
    (by simpa [L] using tendsto_positiveAFirstStageCutoff_div_logCube hN)
    (by simpa [L] using logarithmicHorizon_div_logCube_tendsto hN ht)
    ht
  exact (eventually_positiveAFirstStageCutoff_lt_horizon hN ht).mono
    (fun _ h => Nat.le_of_lt h)

/-- A positive cubic-scale span has its cube-root width at the corresponding
linear logarithmic scale. -/
lemma tendsto_positiveASpan_root_div_log
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

/-- A sublinear power of the second-stage span is negligible compared with
`log N`. This is the `p < 1` remainder in the exponent of the long-prefix
Aïdékon--Hu terms. -/
lemma tendsto_positiveASpan_sublinearPower_div_log
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
lemma tendsto_positiveAAHExponent_div_log_of_logarithmicScales
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t b v c κ p : ℝ}
    (ht : 0 < t) (hp1 : p < 1) :
    Tendsto
      (fun n => ((-b + v) * logarithmOfSampleSize N n +
          c * (((logarithmicHorizon N t n -
            positiveAFirstStageCutoff N n : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
          κ * c ^ p * (((logarithmicHorizon N t n -
            positiveAFirstStageCutoff N n : ℕ) : ℝ) ^ (p / 3))) /
          logarithmOfSampleSize N n)
      atTop (𝓝 (-b + v + c * (t ^ (3⁻¹ : ℝ)))) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let D : ℕ → ℕ := fun n =>
    logarithmicHorizon N t n - positiveAFirstStageCutoff N n
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hDscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    apply tendsto_positiveASpan_cubicRatio_of_stageRatios hL
    · simpa [L] using tendsto_positiveAFirstStageCutoff_div_logCube hN
    · simpa [L] using logarithmicHorizon_div_logCube_tendsto hN ht
    · exact (eventually_positiveAFirstStageCutoff_lt_horizon hN ht).mono
        (fun _ h => Nat.le_of_lt h)
  have hroot := tendsto_positiveASpan_root_div_log hL hDscale ht
  have hsmall := tendsto_positiveASpan_sublinearPower_div_log
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
