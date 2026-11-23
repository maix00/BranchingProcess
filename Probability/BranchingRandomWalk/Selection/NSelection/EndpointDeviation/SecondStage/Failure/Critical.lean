/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Bound
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.Critical.Survival
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Scales

/-!
# Terminal survival in the second-stage critical corridor

## Public declarations

* `eventually_measure_positiveASelectedBRWTerminalEmpty_le_exp_neg_power`:
  for $m_n=\lfloor N_n^a\rfloor$, $H_n/(\log N_n)^3\to t>0$, and admissible
  first-stage parameters with $0<\delta<a-b-2v-3\varepsilon$, the probability
  of an empty terminal population is eventually at most
  $e^{-N_n^\delta}+e^{-N_n^{\delta/2}}$.

This is the terminal survival estimate of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1 for $0<a<1$.
The one-root estimate is Lemma 3.7, equation (3.8).
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Terminal survival for the variable root count and horizon in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1 for $0<a<1$. -/
theorem eventually_measure_positiveASelectedBRWTerminalEmpty_le_exp_neg_power
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {t sigma a b v c ε δ : ℝ}
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (hv : 0 < v) (hvb : v < b) (hc : 0 < c)
    (hε : 0 < ε) (hδ : 0 < δ) (hbudget : δ < a - b - 2 * v - 3 * ε)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
    ∀ᶠ n in atTop,
      let m := Nat.floor ((N n : ℝ) ^ a)
      let P := positiveASelectedBRWPopulation m (positiveAFirstStageCutoff N n) (H n)
        (logarithmOfSampleSize N n) b v c κ
      (finiteRootStepFieldLaw μ m) {field | ¬ (P (H n) field).Nonempty} ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ δ))) +
          ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ (δ / 2)))) := by
  intro κ
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  let K (n : ℕ) := Nat.floor ((N n : ℝ) ^ δ)
  let ell := positiveAFirstStageCutoff N
  let L := logarithmOfSampleSize N
  let D (n : ℕ) := H n - ell n
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hNr
  have hcutoff := tendsto_positiveAFirstStageCutoff_div_logCube hN
  have horderH := (eventually_positiveAFirstStageCutoff_lt_of_logCubeLimit hN ht hH).mono
    (fun _ h => h.le)
  have hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3) atTop (𝓝 t) :=
    tendsto_positiveASpan_cubicRatio_of_stageRatios hL hcutoff hH horderH
  have hD : Tendsto (fun n => (D n : ℝ)) atTop atTop :=
    tendsto_positiveASpan_atTop_of_cubicRatio hL hscale ht
  have hDnat : Tendsto D atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [hD.eventually_ge_atTop (k : ℝ)] with n hn
    exact_mod_cast hn
  let R := t ^ (3⁻¹ : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hratio := (tendsto_positiveASpan_root_div_log hL hscale ht).eventually
    (Iio_mem_nhds (show t ^ (3⁻¹ : ℝ) < R by dsimp [R]; linarith))
  let α := -(δ / 4) / R
  have hα : α < 0 := div_neg_of_neg_of_pos (by linarith) hR
  have hrootBase := CriticalCorridor.eventually_survival_ge_exp_mul_cubeRoot
    realPotential μ hboundary hcross hcentered hsigma hc hv hα
  dsimp only at hrootBase
  have hroot := hDnat.eventually hrootBase
  have hq : ∀ᶠ n in atTop,
      (N n : ℝ) ^ (-(δ / 4)) ≤ (offspringFieldLaw μ).real
        (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0
          (positiveASecondStageCorridor (D n) κ c v)) := by
    filter_upwards [hroot, hratio, hL.eventually_gt_atTop 0,
      hN.eventually_gt_atTop 0, hDnat.eventually_gt_atTop 0] with n hr htube hLn hNn hDn
    have hrp : (0 : ℝ) < D n := by exact_mod_cast hDn
    have hslope : positiveASecondStageSlope κ c (D n) =
        κ / (positiveASecondStageWidth c (D n)) ^ 2 := by
      unfold positiveASecondStageSlope positiveASecondStageWidth
      have hp : (((D n : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ)) = (D n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hrp.le]
        norm_num
      rw [mul_pow, hp, show (-2 / 3 : ℝ) = -(2 / 3) by ring, Real.rpow_neg hrp.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast hNn
    refine le_trans (b := Real.exp (α * (D n : ℝ) ^ (1 / 3 : ℝ))) ?_ ?_
    · rw [Real.rpow_def_of_pos hNpos]
      apply Real.exp_le_exp.mpr
      have hDupper := (div_lt_iff₀ hLn).mp htube
      have h := mul_le_mul_of_nonpos_left hDupper.le hα.le
      have hαR : α * R = -(δ / 4) := div_mul_cancel₀ _ hR.ne'
      rw [← mul_assoc, hαR] at h
      rw [mul_comm (Real.log (N n : ℝ))]
      simpa only [L, logarithmOfSampleSize, show (3⁻¹ : ℝ) = 1 / 3 by norm_num] using h
    · rw [positiveASecondStageCorridor, hslope, div_mul_eq_mul_div₀ κ]
      exact hr
  have hlarge := Asymptotics.eventually_floor_rpow_mul_ge
    (y := fun n => (N n : ℝ) ^ (-(δ / 4))) hNr
    (a := δ) (r := -(δ / 4)) (δ := δ / 2) (C := 1) hδ (by linarith) (Eventually.of_forall fun _ => le_rfl)
  let ν := tiltedPotentialLaw realPotential (-1) μ
  let _ := tiltedPotentialLaw_isProbability realPotential μ hboundary
  have hlow := eventually_measure_positiveASelectedBRWEnoughRoots_compl_le_exp_neg_power
    hN μ hboundary hcross ν rfl hcentered hsigma ha hb hv hvb hε hbudget
    (c := c) (κ := κ) H (fun _ => inferInstance)
  filter_upwards [hlow, hq, hlarge, horderH, hL.eventually_gt_atTop 0,
    (tendsto_positiveAFirstStageCutoff_atTop hN).eventually_gt_atTop 0,
    hN.eventually_ge_atTop 1] with n hl hqn hbig hHn hLn hell hNn
  let _ := horder n
  have hKnm : K n ≤ m n := by
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hNn) (by linarith)
  have hfail := measure_positiveASelectedBRWTerminalEmpty_le_of_survival
    (m n) (K n) (ell n) (H n) hKnm (L n) b v c κ hell hHn
    (mul_nonneg hb.le hLn.le) μ hboundary ((N n : ℝ) ^ (-(δ / 4)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hqn
  refine hfail.trans (add_le_add hl ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [one_mul] at hbig
  simpa only [neg_mul] using neg_le_neg hbig

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
