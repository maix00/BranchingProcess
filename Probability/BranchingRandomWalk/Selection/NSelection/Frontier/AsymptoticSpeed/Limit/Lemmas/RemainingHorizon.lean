/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit

/-!
# Endpoint expectation after a short entrance time

## Internal proof declarations

* `eventually_endpointMean_sub_horizon_le`: for $0<a<1$, if
  $H_N/\log^3N\to t>0$ and $T_N=o(\log^3N)$, then
  $\mathbb E[M_{H_N-i}^{N|a}]/\log N\le-a+\pi^2\sigma^2t/2+\varepsilon$
  simultaneously for $0\le i\le T_N$ eventually.

This is the uniform remaining-horizon use of Theorem 1.1 in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Theorem 1.2.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

lemma eventually_endpointMean_sub_horizon_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) (hε : 0 < ε)
    {N H T : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    ∀ᶠ n in atTop, ∀ i ≤ T n,
      (∫ field, @countableRootEndpointMinimum (m n) (N n) (H n - i)
        (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / Real.log (N n : ℝ) ∂P) ≤
        -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε := by
  intro P m
  let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
  let logN := fun n => Real.log (N n : ℝ)
  let M n i := ∫ field, @countableRootEndpointMinimum (m n) (N n) (H n - i)
    (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / logN n ∂P
  change ∀ᶠ n in atTop, ∀ i ≤ T n, M n i ≤ c + ε
  by_contra! h
  rw [frequently_atTop] at h
  choose n hn i hi hbad using h
  have hnTop : Tendsto n atTop atTop := tendsto_atTop.2 fun k =>
    (eventually_ge_atTop k).mono fun j hj => hj.trans (hn j)
  have hlog : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hTH : ∀ᶠ j in atTop, T j ≤ H j := by
    filter_upwards [hlog.eventually_gt_atTop 0,
      hT.eventually (Iio_mem_nhds (show (0 : ℝ) < t / 2 by positivity)),
      hH.eventually (Ioi_mem_nhds (show t / 2 < t by linarith))] with j hLj hs hh
    exact_mod_cast ((div_lt_div_iff_of_pos_right (pow_pos hLj 3)).mp (hs.trans hh)).le
  have hshort : Tendsto (fun k => (i k : ℝ) / logN (n k) ^ 3) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (hT.comp hnTop)
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      positivity
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi k) (pow_pos hk 3).le
  have hremaining :
      Tendsto (fun k => ((H (n k) - i k : ℕ) : ℝ) / logN (n k) ^ 3) atTop (𝓝 t) := by
    have hdiff := (hH.comp hnTop).sub hshort
    rw [sub_zero] at hdiff
    apply hdiff.congr'
    filter_upwards [hnTop.eventually hTH] with k hk
    simp [logN, Nat.cast_sub ((hi k).trans hk), sub_div]
  have hmean : Tendsto (fun k => M (n k) (i k)) atTop (𝓝 c) :=
    tendsto_integral_countableRootEndpointMinimum_div L hsuper hnonempty hboundary
      hcross hfour hsigma hspine ⟨ha.le, ha1.le⟩ ht
      (fun he => (ha.ne' he).elim) (fun k => hcapacity (n k)) (hN.comp hnTop) hremaining
  rw [tendsto_order] at hmean
  obtain ⟨k, hk⟩ := (hmean.2 _ (lt_add_of_pos_right c hε)).exists
  exact (hbad k).not_gt hk

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
