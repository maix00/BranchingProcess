/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.SpinalWeight
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.CountableRoots
import Analysis.Asymptotics.Power.FloorProduct
import Analysis.Asymptotics.Sequence.ExponentialSum
import Analysis.Asymptotics.Sequence.LogarithmicScale
import Analysis.Asymptotics.Scale.Power.Basic

/-!
# Polynomial decay from the weak-tail affine endpoint budget

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_endpointUpperTail_of_weakTail_logarithmicMargins`:
  for the internal affine-corridor parameters satisfying strict root, capacity
  and terminal margins, the existing first-N endpoint minimum from `⌊N^A⌋`
  roots has probability at most `exp(-p log N)`, for some `p>0`.

This specializes the cutoff moment bound of B. Mallein, *N-branching random
walk with α-stable spine*, Lemma 3.4, arXiv:1503.03762v2, to the logarithmic
endpoint scales of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1.
Generic floor-product, power, logarithm and finite-exponential-sum limits are
used directly from their analysis owners.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Filter MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

lemma eventually_endpointUpperTail_of_weakTail_logarithmicMargins
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (htail : HasSpinalWeightTail realPotential μ)
    {σ A T ζ w α a b ρ dUpper dLower β : ℝ}
    (hσ : 0 < σ)
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2))
    (hA : 0 < A) (hT : 0 < T) (hw : 0 < w) (hα : 0 < α)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ)
    (hdUpper : 0 < dUpper) (hUpper : dUpper < (Real.pi ^ 2 / 2) * σ ^ 2)
    (hLower : (Real.pi ^ 2 / 2) * σ ^ 2 < dLower)
    (hβ : α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * (T / w ^ 3) < β)
    (hroot : β * w < A)
    (hcap : A + (1 / 2 - a) * w +
      max ((Real.pi ^ 2 / 2) * σ ^ 2 - dUpper) 0 * T / w ^ 2 < 1)
    (hend : (b + ρ - a) * w + ((Real.pi ^ 2 / 2) * σ ^ 2) * T / w ^ 2 < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 T))
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin ⌊(N n : ℝ) ^ A⌋₊) ℕ)) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | ζ * Real.log (N n : ℝ) ≤
          @countableRootEndpointMinimum ⌊(N n : ℝ) ^ A⌋₊ (N n) (H n) (horder n) field} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  let ℓ n := Real.log (N n : ℝ)
  let L n := w * ℓ n
  let m n := ⌊(N n : ℝ) ^ A⌋₊
  let κ := (Real.pi ^ 2 / 2) * σ ^ 2
  let U n := (b + ρ - a) * L n + κ * (H n : ℝ) / L n ^ 2
  let B n := -(a + 1 / 2) * L n + L n + L n ^ (1 / 2 : ℝ) +
    max (κ - dUpper) 0 * (H n : ℝ) / L n ^ 2
  let E n := A * ℓ n + Real.log ((H n : ℝ) + 1) + B n
  let γ := A + (1 / 2 - a) * w + max (κ - dUpper) 0 * T / w ^ 2
  let p := (1 - γ) / 4
  have hγ : γ < 1 := hcap
  have hp : 0 < p := div_pos (sub_pos.mpr hγ) (by norm_num)
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hℓ : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp hNr
  have hL : Tendsto L atTop atTop := hℓ.const_mul_atTop hw
  have hpos := hℓ.eventually_gt_atTop 0
  have hNpos := hN.eventually_gt_atTop 0
  have hH' : Tendsto (fun n => (H n : ℝ) / L n ^ 3) atTop (𝓝 (T / w ^ 3)) := by
    apply (hH.div_const (w ^ 3)).congr'
    filter_upwards [hpos] with n hn
    dsimp [L, ℓ]
    field_simp
  have hraw := eventually_measure_endpointMinimum_gt_le_affineBudget_of_spinalWeightTail
    μ hboundary hcentered hσ htail hα hdUpper hUpper hLower hUpper.le
    ha ha' hb hb' hρ (div_pos hT (pow_pos hw 3)) hβ hL hH' hNpos horder
  have htime : Tendsto (fun n => (H n : ℝ) / L n ^ 2 / ℓ n) atTop (𝓝 (T / w ^ 2)) := by
    apply (hH.div_const (w ^ 2)).congr'
    filter_upwards [hpos] with n hn
    dsimp [L, ℓ]
    field_simp
  have hunit : Tendsto (fun n => ℓ n / ℓ n ^ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos] with n hn
    simp [hn.ne']
  have hsqrt₀ := Asymptotics.tendsto_rpow_div_of_ratio_limit hℓ hunit one_ne_zero
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsqrt : Tendsto (fun n => L n ^ (1 / 2 : ℝ) / ℓ n) atTop (𝓝 0) := by
    have h := hsqrt₀.const_mul (w ^ (1 / 2 : ℝ))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hpos] with n hn
    dsimp [L]
    rw [Real.mul_rpow hw.le hn.le]
    ring
  have hHbound : ∀ᶠ n in atTop, (H n : ℝ) ≤ (T + 1) * ℓ n ^ (3 : ℝ) := by
    filter_upwards [hpos, hH.eventually (Iio_mem_nhds (lt_add_one T))] with n hn hratio
    rw [show ℓ n ^ (3 : ℝ) = ℓ n ^ (3 : ℕ) from Real.rpow_ofNat _ _]
    exact ((div_lt_iff₀ (pow_pos hn 3)).1 hratio).le
  have hlogH := Asymptotics.tendsto_log_add_one_div_scale_of_power_bound hℓ
    (Eventually.of_forall fun n => Nat.cast_nonneg (H n)) (by linarith : 0 ≤ T + 1)
    (by norm_num : (0 : ℝ) < 3) hHbound
  have hERate : Tendsto (fun n => E n / ℓ n) atTop (𝓝 γ) := by
    have h := (((tendsto_const_nhds (x := A + (1 / 2 - a) * w)).add hlogH).add hsqrt).add
      (htime.const_mul (max (κ - dUpper) 0))
    simp only [add_zero] at h
    rw [show A + (1 / 2 - a) * w + max (κ - dUpper) 0 * (T / w ^ 2) = γ by dsimp [γ]; ring] at h
    apply h.congr'
    filter_upwards [hpos] with n hn
    dsimp [E, B, L]
    field_simp; ring
  have hURate : Tendsto (fun n => U n / ℓ n) atTop
      (𝓝 ((b + ρ - a) * w + κ * T / w ^ 2)) := by
    have h := (tendsto_const_nhds (x := (b + ρ - a) * w)).add (htime.const_mul κ)
    rw [show (b + ρ - a) * w + κ * (T / w ^ 2) =
      (b + ρ - a) * w + κ * T / w ^ 2 by ring] at h
    apply h.congr'
    filter_upwards [hpos] with n hn
    dsimp [U, L]
    field_simp
  have hthreshold := hURate.eventually (Iio_mem_nhds hend)
  have hEgap := hERate.eventually (Iio_mem_nhds (show γ < 1 - 2 * p by dsimp [p]; linarith only [hγ]))
  let δ := (A - β * w) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hqpow : ∀ᶠ n in atTop, (N n : ℝ) ^ (-(β * w)) ≤ Real.exp (-β * L n) := by
    filter_upwards [hNpos] with n hn
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
    apply le_of_eq
    congr 1
    dsimp [L, ℓ]
    ring
  have hrootCount := Asymptotics.eventually_floor_rpow_mul_ge (C := 1) hNr hA
    (show δ < A + -(β * w) by dsimp [δ]; linarith) hqpow
  have hsmall := ((isLittleO_log_rpow_atTop hδ).comp_tendsto hNr).bound
    (show 0 < (1 / (2 * p) : ℝ) by positivity)
  have hrootBound : ∀ᶠ n in atTop,
      Real.exp (-(m n : ℝ) * Real.exp (-β * L n)) ≤ Real.exp (-2 * p * ℓ n) := by
    filter_upwards [hrootCount, hsmall, hpos] with n hn hs hnpos
    change ‖ℓ n‖ ≤ (1 / (2 * p)) * ‖(N n : ℝ) ^ δ‖ at hs
    rw [Real.norm_of_nonneg hnpos.le, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hs
    have hlog := (le_div_iff₀ (by positivity : 0 < 2 * p)).1 (by simpa [div_eq_mul_inv, mul_comm] using hs)
    simp only [one_mul] at hn
    apply Real.exp_le_exp.mpr
    dsimp [m] at *
    nlinarith [hlog.trans hn]
  have hsum : ∀ᶠ n in atTop,
      Real.exp (-2 * p * ℓ n) + Real.exp (-2 * p * ℓ n) ≤ Real.exp (-p * ℓ n) := by
    have h := Asymptotics.eventually_sum_exp_le_exp_mul_of_uniform_gap
      (Finset.univ : Finset (Fin 2)) ℓ (fun n _ => -2 * p * ℓ n)
      (-p) (p / 2) (by positivity) hℓ (by
        intro i _
        filter_upwards [hpos] with n hn
        rw [mul_div_cancel_right₀ _ hn.ne']
        linarith)
    simpa [two_mul] using h
  refine ⟨p, hp, ?_⟩
  filter_upwards [hraw, hthreshold, hEgap, hrootBound, hsum, hpos, hNpos]
    with n hn htN hEg hrN hsumN hℓn hNn
  let := horder n
  have hNnr : 0 < (N n : ℝ) := by exact_mod_cast hNn
  have hm : (m n : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (A * ℓ n)) := by
    rw [← ENNReal.ofReal_natCast]
    refine (ENNReal.ofReal_le_ofReal (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq ?_
    rw [Real.rpow_def_of_pos hNnr]
    congr 2
    dsimp [ℓ]
    ring
  have hcount : ((H n : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (B n)) =
      ENNReal.ofReal (Real.exp (Real.log ((H n : ℝ) + 1) + B n)) := by
    have hc : (H n : ℝ≥0∞) + 1 = ENNReal.ofReal ((H n : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [hc, ← ENNReal.ofReal_mul (by positivity)]
    apply congrArg ENNReal.ofReal
    calc
      _ = Real.exp (Real.log ((H n : ℝ) + 1)) * Real.exp (B n) := by
        rw [Real.exp_log (by positivity)]
      _ = _ := (Real.exp_add _ _).symm
  have hnum : (m n : ℝ≥0∞) * ((H n : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (B n)) ≤
      ENNReal.ofReal (Real.exp ((1 - 2 * p) * ℓ n)) := by
    calc
      _ = (m n : ℝ≥0∞) * (((H n : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (B n))) := mul_assoc _ _ _
      _ ≤ ENNReal.ofReal (Real.exp (A * ℓ n)) *
          ENNReal.ofReal (Real.exp (Real.log ((H n : ℝ) + 1) + B n)) := mul_le_mul' hm hcount.le
      _ = ENNReal.ofReal (Real.exp (E n)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        dsimp [E]
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ((div_lt_iff₀ hℓn).1 hEg).le)
  have hden : (N n : ℝ≥0∞) ≤ (N n + 1 : ℕ) := by exact_mod_cast Nat.le_succ (N n)
  have hidDen : ENNReal.ofReal (Real.exp (-2 * p * ℓ n)) * (N n : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp ((1 - 2 * p) * ℓ n)) := by
    rw [← ENNReal.ofReal_natCast, show (N n : ℝ) = Real.exp (ℓ n) from (Real.exp_log hNnr).symm,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2; ring
  have hcapN : (m n : ℝ≥0∞) * ((H n : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (B n)) /
      (N n + 1 : ℕ) ≤ ENNReal.ofReal (Real.exp (-2 * p * ℓ n)) := by
    apply (ENNReal.div_le_iff (by positivity) (ENNReal.natCast_ne_top _)).2
    exact hnum.trans (hidDen.symm.le.trans (mul_le_mul' le_rfl hden))
  have hbudget := hn.trans (add_le_add (ENNReal.ofReal_le_ofReal hrN) hcapN)
  have hsumENN : ENNReal.ofReal (Real.exp (-2 * p * ℓ n)) +
      ENNReal.ofReal (Real.exp (-2 * p * ℓ n)) ≤ ENNReal.ofReal (Real.exp (-p * ℓ n)) := by
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsumN
  have hbudget' := hbudget.trans hsumENN
  have hthresholdN : U n < ζ * ℓ n := (div_lt_iff₀ hℓn).1 htN
  have hmap := congrArg (fun law : Measure ℝ => law (Set.Ici (ζ * ℓ n)))
    (countableRootEndpointMinimum_map_eq μ (m n) (N n) (H n))
  rw [Measure.map_apply (measurable_countableRootEndpointMinimum (m n) (N n) (H n)) measurableSet_Ici,
    Measure.map_apply (measurable_firstNSelectedEndpointMinimum (m n) (N n) (H n)) measurableSet_Ici] at hmap
  change (RootIndexed.stepFieldLaw (Root := ℕ) μ)
    ((countableRootEndpointMinimum (m n) (N n) (H n)) ⁻¹' Set.Ici (ζ * ℓ n)) ≤ _
  rw [hmap]
  refine (measure_mono fun field hf => ?_).trans hbudget'
  exact hthresholdN.trans_le hf

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
