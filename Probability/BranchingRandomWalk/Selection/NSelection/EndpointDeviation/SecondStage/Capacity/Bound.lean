/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Cutoff
public import Probability.Distributions.Moments.Real
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Basic
public import Probability.BranchingRandomWalk.Spine.Tilted.Law
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Scales
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Capacity.Lemmas.Critical
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Capacity.Lemmas.PolynomialDecay
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic
import Analysis.Asymptotics.Sequence.LogarithmicScale

/-!
# Polynomial capacity bound for the critical restarted corridor

## Public declarations

* `eventually_positiveASelectedBRWCapacityFailure_le_polynomial_of_criticalTube`:
  for $0<a<1$, $H_n/(\log N_n)^3\to t>0$ and
  $a-b+v+ct^{1/3}<1$, the critical two-stage population exceeds capacity
  $N_n$ by time $H_n$ with probability at most $N_n^{-p}$ eventually,
  for some $p>0$.

This is the population bound of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, proof of Theorem 1.1 for $0<a<1$. The sum of expected generation
sizes is bounded using the critical drift from Chapter 3, Lemma 3.7.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The capacity term in the proof of Wang Yiyang's Theorem 1.1, Chapter 4
of *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026). -/
theorem eventually_positiveASelectedBRWCapacityFailure_le_polynomial_of_criticalTube
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    {sigma a b v c t : ℝ}
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (ha : a < 1) (hb : 0 ≤ b) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c) (ht : 0 < t)
    (hmargin : a + (-b + v + c * t ^ (3⁻¹ : ℝ)) < 1)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      let m := Nat.floor ((N n : ℝ) ^ a)
      let P := positiveASelectedBRWPopulation m (positiveAFirstStageCutoff N n) (H n)
        (logarithmOfSampleSize N n) b v c κ
      (finiteRootStepFieldLaw μ m) (P.capacityEvent (N n) (H n))ᶜ ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  intro κ
  let L := logarithmOfSampleSize N
  let ell := positiveAFirstStageCutoff N
  let D (n : ℕ) := H n - ell n
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  let r := t ^ (3⁻¹ : ℝ)
  let w (n : ℕ) := c * (D n : ℝ) ^ (3⁻¹ : ℝ)
  let ν := tiltedPotentialLaw realPotential (-1) μ
  let _ := tiltedPotentialLaw_isProbability realPotential μ hboundary
  have hν : tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν := rfl
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hr : 0 < r := Real.rpow_pos_of_pos ht _
  have hmargin' : a + (-b + v + c * r) < 1 := hmargin
  let s := min (κ / 2) ((1 - (a + (-b + v + c * r))) * c ^ 2 / (2 * r))
  have hs : 0 < s := lt_min (by positivity) (div_pos (mul_pos (by linarith) (by positivity))
    (by positivity))
  have hsκ : s < κ := (min_le_left _ _).trans_lt (by linarith)
  have hsMargin : s / c ^ 2 * r ≤ (1 - (a + (-b + v + c * r))) / 2 := by
    have hc₂ : 0 < c ^ 2 := by positivity
    have h := (le_div_iff₀ (show 0 < 2 * r by positivity)).mp
      (show s ≤ _ from min_le_right _ _)
    have hle : s * r ≤ ((1 - (a + (-b + v + c * r))) / 2) * c ^ 2 := by
      linarith only [h]
    rw [div_mul_eq_mul_div₀]
    exact (div_le_iff₀ hc₂).mpr hle
  let q := -b + v + (c + s / c ^ 2) * r
  have hq : a + q < 1 := by
    dsimp [q]
    nlinarith
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hstrict := eventually_positiveAFirstStageCutoff_lt_of_logCubeLimit hN ht hH
  have horder := hstrict.mono (fun _ hn => hn.le)
  have hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3) atTop (𝓝 t) :=
    tendsto_positiveASpan_cubicRatio_of_stageRatios hL
      (tendsto_positiveAFirstStageCutoff_div_logCube hN) hH horder
  have hD := tendsto_positiveASpan_atTop_of_cubicRatio hL hscale ht
  have hw : Tendsto w atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (3⁻¹ : ℝ))).comp hD |>.const_mul_atTop hc
  obtain ⟨w₀, hw₀, hprefix⟩ := exists_driftedTubeProbability_le_exp_of_finiteVariance
    ν hcentered (sq_pos_of_pos hsigma) (by norm_num : (0 : ℝ) < 1 / 2)
    hκ.le (sub_pos.mpr hsκ) (show κ - s < κ by linarith)
  let E (n : ℕ) := (-b + v) * L n + w n + w n ^ (1 / 2 : ℝ) +
    s * (D n : ℝ) / w n ^ 2
  have hsquare : Tendsto (fun n => w n ^ (1 / 2 : ℝ) / L n) atTop (𝓝 0) := by
    have h := (tendsto_positiveASpan_sublinearPower_div_log hL hscale ht
      (p := 1 / 2) (by norm_num)).const_mul (c ^ (1 / 2 : ℝ))
    simp only [mul_zero] at h
    apply h.congr
    intro n
    rw [show w n ^ (1 / 2 : ℝ) = c ^ (1 / 2 : ℝ) * (D n : ℝ) ^ ((1 / 2 : ℝ) / 3) by
      dsimp [w]
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 2
      norm_num]
    ring
  have hERate : Tendsto (fun n => E n / L n) atTop (𝓝 q) := by
    have h := (tendsto_positiveASpan_root_div_log hL hscale ht).const_mul (c + s / c ^ 2)
    have htarget : Tendsto
        (fun n => (-b + v) + ((c + s / c ^ 2) * ((D n : ℝ) ^ (3⁻¹ : ℝ) / L n) +
          w n ^ (1 / 2 : ℝ) / L n)) atTop (𝓝 q) := by
      simpa only [q, r, add_zero] using (tendsto_const_nhds (x := -b + v)).add (h.add hsquare)
    apply htarget.congr'
    filter_upwards [hstrict, hL.eventually_gt_atTop 0] with n hn hLn
    have hDr : (0 : ℝ) < D n := by exact_mod_cast Nat.sub_pos_of_lt hn
    have hwidthSq : w n ^ 2 = c ^ 2 * (D n : ℝ) ^ (2 / 3 : ℝ) := by
      dsimp [w]
      rw [mul_pow, ← Real.rpow_natCast ((D n : ℝ) ^ (3⁻¹ : ℝ)) 2,
        ← Real.rpow_mul hDr.le]
      congr 2
      norm_num
    have hdiv : (D n : ℝ) / (D n : ℝ) ^ (2 / 3 : ℝ) = (D n : ℝ) ^ (3⁻¹ : ℝ) := by
      rw [show (3⁻¹ : ℝ) = 1 - 2 / 3 by norm_num, Real.rpow_sub hDr, Real.rpow_one]
    dsimp [E]
    rw [hwidthSq, show s * (D n : ℝ) / (c ^ 2 * (D n : ℝ) ^ (2 / 3 : ℝ)) =
      (s / c ^ 2) * ((D n : ℝ) / (D n : ℝ) ^ (2 / 3 : ℝ)) by ring, hdiv]
    dsimp [w]
    field_simp
    ring
  have hcount : ∀ᶠ n in atTop, (H n : ℝ) ≤ (t + 1) * L n ^ (3 : ℝ) := by
    filter_upwards [hH.eventually (Iio_mem_nhds (show t < t + 1 by linarith)),
      hL.eventually_gt_atTop 0] with n hn hLn
    rw [show L n ^ (3 : ℝ) = L n ^ (3 : ℕ) by simpa only [Nat.cast_ofNat] using Real.rpow_natCast (L n) 3]
    exact ((div_lt_iff₀ (pow_pos hLn 3)).mp hn).le
  have hcountLog := Asymptotics.tendsto_log_add_one_div_scale_of_power_bound hL
    (Filter.Eventually.of_forall (fun n => Nat.cast_nonneg (H n))) (by linarith : 0 ≤ t + 1)
    (by norm_num : (0 : ℝ) < 3) hcount
  have hDcount : ∀ᶠ n in atTop, (D n : ℝ) ≤ (t + 1) * L n ^ (3 : ℝ) := by
    filter_upwards [hcount] with n hn
    exact (Nat.cast_le.mpr (Nat.sub_le (H n) (ell n))).trans hn
  have hDLog := Asymptotics.tendsto_log_add_one_div_scale_of_power_bound hL
    (Filter.Eventually.of_forall (fun n => Nat.cast_nonneg (D n))) (by linarith : 0 ≤ t + 1)
    (by norm_num : (0 : ℝ) < 3) hDcount
  let P (n : ℕ) := (finiteRootStepFieldLaw μ (m n))
    ((positiveASelectedBRWPopulation (m n) (ell n) (H n) (L n) b v c κ).capacityEvent
      (N n) (H n))ᶜ
  have hraw : ∀ᶠ n in atTop,
      P n ≤ (m n : ℝ≥0∞) * (((ell n + 1 : ℕ) : ℝ≥0∞) + (D n : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (E n))) / (N n + 1 : ℕ) := by
    filter_upwards [hstrict, (tendsto_positiveAFirstStageCutoff_atTop hN).eventually_gt_atTop 0,
      hL.eventually_gt_atTop 0, hw.eventually_ge_atTop w₀] with n hn hell hLn hwn
    refine measure_positiveASelectedBRW_capacityEvent_compl_le_of_criticalTube
      (m n) (ell n) (H n) (N n) (L n) b v c κ s hell hn hb hLn.le hvb hvc hc hs.le μ hboundary ?_
    intro j
    change tiltedIncrementFieldLaw realPotential μ (driftedTubeEvent j (w n) κ 0) ≤ _
    rw [hν, ← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hprefix (w n) hwn 0 (by linarith [hw₀.trans hwn]) le_rfl j)
  exact eventually_capacityFailure_le_polynomial_of_twoPhaseMomentBound
    (P := P) (m := m) (ell := ell) (ellN := H) (N := N) (E := E)
    hN horder hcountLog hDLog hERate ha hq
    (Eventually.of_forall fun n => Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hraw

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
