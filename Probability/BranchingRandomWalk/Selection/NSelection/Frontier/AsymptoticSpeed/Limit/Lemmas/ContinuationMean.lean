/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.FirstMoment

/-!
# Upper expectation of the centered continuation

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.eventually_endpointMean_sub_horizon_le_of_firstMoment`: the upper mean
  bound holds uniformly for $H_N-i$, $0\le i\le T_N$, when
  $T_N=o(\log^3 N)$.

The complete endpoint `L¹` and expectation limits are public in
`EndpointDeviation/Endpoint/Sequence/FirstMoment.lean`. This proof calls that
entry and extracts a deterministic violating sequence if uniformity fails.
It is the remaining-horizon step of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.2, under Mallein's weak reproductive condition
(Theorem 1.1 (1.9), arXiv:1503.03762v2).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

/-- Uniform upper mean for deterministic horizons in the deadline window. -/
lemma eventually_endpointMean_sub_horizon_le_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) (hε : 0 < ε)
    {N H T : ℕ → ℕ}
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
  have hmean := tendsto_integral_countableRootEndpointMinimum_div_of_spinalWeightTail L
    hnonempty hboundary htail hfirst hsigma hspine ha ha1.le ht
    (hN.comp hnTop) hremaining
  obtain ⟨k, hk⟩ := (hmean.eventually (Iio_mem_nhds
    (show -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < c + ε / 2 by dsimp [c]; linarith))).exists
  change M (n k) (i k) < c + ε / 2 at hk
  linarith [hbad k]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
