/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.CountableRoots
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Capacity.Bound
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Critical
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Population.Embedding
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Parameters
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Scales

/-!
# Endpoint upper tail with a positive initial exponent

## Public declarations

* `eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent`:
  when $0<a<1$, $H_n/(\log N_n)^3\to t>0$, and
  $\zeta>-a+\pi^2\sigma^2t/2$, the minimum $M_n$ from
  $\lfloor N_n^a\rfloor$ zero-position roots at capacity $N_n$ satisfies
  $\mathbb P(M_n\ge\zeta\log N_n)\le N_n^{-p}$ eventually for some $p>0$.

This is the positive-exponent case of the endpoint upper-tail estimate in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, proof of Theorem 1.1.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The case $0<a<1$ of the upper-tail estimate in Wang Yiyang's
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1. -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | ζ * Real.log (N n : ℝ) ≤
          @countableRootEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n) (H n) (horder n)
            field} ≤ ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  let r := t ^ (3⁻¹ : ℝ)
  let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
  have hr : 0 < r := Real.rpow_pos_of_pos ht _
  have hrcube : r ^ 3 = t := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      show (3⁻¹ : ℝ) * ↑(3 : ℕ) = 1 by norm_num, Real.rpow_one]
  obtain ⟨b, v, c, hb, _, hv, hvb, hvc, hc, _, hmargin, hendpoint, hbudget⟩ :=
    exists_positiveAParameters a t r (sigma ^ 2) ζ ha ht hr hrcube (sq_nonneg _) hgap
  have hmargin' : a + (-b + v + c * r) < 1 := by linarith
  obtain ⟨q, hq, hcap⟩ := eventually_positiveASelectedBRWCapacityFailure_le_polynomial_of_criticalTube
    hN μ hboundary hcentered hsigma ha1 hb.le hvb.le hc hvc ht hmargin' hH
  let δ := (a - b - 2 * v) / 2
  let ε := (a - b - 2 * v) / 12
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hterminal := eventually_measure_positiveASelectedBRWTerminalEmpty_le_exp_neg_power
    hN μ hboundary hcross hcentered hsigma ht ha hb hv hvb hc hε hδ
      (by dsimp [δ, ε]; linarith) hH horder
  let L := logarithmOfSampleSize N
  let ell := positiveAFirstStageCutoff N
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  let D (n : ℕ) := H n - ell n
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hNr
  have hstrict := eventually_positiveAFirstStageCutoff_lt_of_logCubeLimit hN ht hH
  have hspan := tendsto_positiveASpan_cubicRatio_of_stageRatios hL
    (tendsto_positiveAFirstStageCutoff_div_logCube hN) hH (hstrict.mono (fun _ h => h.le))
  have hroot := tendsto_positiveASpan_root_div_log hL hspan ht
  have htrend := (hroot.const_mul (κ / c ^ 2 + v)).const_add (-b + v)
  have hendpoint' : -b + v + (κ / c ^ 2 + v) * r < ζ := by
    have hs : κ * (c⁻¹ ^ 2 * r) = κ / c ^ 2 * r := by ring
    change -b + κ * (c⁻¹ ^ 2 * r) + 2 * v * (1 + r) < ζ at hendpoint
    rw [hs] at hendpoint
    nlinarith
  have hthreshold := htrend.eventually (Iio_mem_nhds hendpoint')
  have hcompare (x : ℝ) (hx : 0 < x) :
      ∀ᶠ n in atTop, q * L n ≤ (N n : ℝ) ^ x := by
    have hsmall := ((isLittleO_log_rpow_atTop hx).comp_tendsto hNr).bound
      (show 0 < (1 / q : ℝ) from one_div_pos.mpr hq)
    filter_upwards [hsmall, hL.eventually_gt_atTop 0] with n hn hLn
    change ‖L n‖ ≤ (1 / q) * ‖(N n : ℝ) ^ x‖ at hn
    rw [Real.norm_of_nonneg hLn.le, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      at hn
    have hdiv : L n ≤ (N n : ℝ) ^ x / q := by
      convert hn using 1
      ring
    simpa only [mul_comm q] using (le_div_iff₀ hq).mp hdiv
  have hfactorTrend := Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity : 0 < q / 2))
  have hfactor : ∀ᶠ n in atTop, 3 ≤ Real.exp (q / 2 * L n) :=
    hfactorTrend.eventually_ge_atTop 3
  refine ⟨q / 2, by positivity, ?_⟩
  filter_upwards [hcap, hterminal, hstrict, hthreshold, hL.eventually_gt_atTop 0,
    (tendsto_positiveAFirstStageCutoff_atTop hN).eventually_gt_atTop 0,
    hcompare δ hδ, hcompare (δ / 2) (by positivity), hfactor]
    with n hcapN hterminalN hstrictN hthresholdN hLn hellN hpow₁ hpow₂ hfactorN
  let _ := horder n
  have hposition : (-b + v) * L n + (κ / c ^ 2 + v) * (D n : ℝ) ^ (3⁻¹ : ℝ) < ζ * L n := by
    apply (div_lt_iff₀ hLn).mp
    calc
      _ = -b + v + (κ / c ^ 2 + v) * ((D n : ℝ) ^ (3⁻¹ : ℝ) / L n) := by
        field_simp
      _ < ζ := hthresholdN
  have hmeasure := measure_firstN_endpointHigh_le_terminalEmpty_add_capacityFailure
    (m n) (N n) (ell n) (H n) (L n) b v c κ (ζ * L n)
    hellN hstrictN (by dsimp [κ]; positivity) hposition μ hboundary
  have hmap := congrArg (fun law : Measure ℝ => law (Set.Ici (ζ * L n)))
    (countableRootEndpointMinimum_map_eq μ (m n) (N n) (H n))
  have hE : MeasurableSet (Set.Ici (ζ * L n)) := measurableSet_Ici
  rw [Measure.map_apply (measurable_countableRootEndpointMinimum (m n) (N n) (H n)) hE,
    Measure.map_apply (measurable_firstNSelectedEndpointMinimum (m n) (N n) (H n)) hE] at hmap
  change (RootIndexed.stepFieldLaw (Root := ℕ) μ)
    ((countableRootEndpointMinimum (m n) (N n) (H n)) ⁻¹' Set.Ici (ζ * L n)) ≤ _
  rw [hmap]
  have hpow (x : ℝ) (hx : q * L n ≤ (N n : ℝ) ^ x) :
      ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ x))) ≤ ENNReal.ofReal (Real.exp (-q * L n)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  let Q := ENNReal.ofReal (Real.exp (-q * L n))
  have hsum : ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ δ))) +
      ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ (δ / 2)))) + Q ≤ Q + Q + Q :=
    add_le_add (add_le_add (hpow δ hpow₁) (hpow (δ / 2) hpow₂)) le_rfl
  refine hmeasure.trans ((add_le_add hterminalN hcapN).trans (hsum.trans ?_))
  suffices hh : Real.exp (-q * L n) + Real.exp (-q * L n) + Real.exp (-q * L n) ≤
      Real.exp (-(q / 2) * L n) by
    dsimp only [Q]
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),
      ← ENNReal.ofReal_add (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hh
  calc
    _ = 3 * Real.exp (-q * L n) := by ring
    _ ≤ Real.exp (q / 2 * L n) * Real.exp (-q * L n) :=
      mul_le_mul_of_nonneg_right hfactorN (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
