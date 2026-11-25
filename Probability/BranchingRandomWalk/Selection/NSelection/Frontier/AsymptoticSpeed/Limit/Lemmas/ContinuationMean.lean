/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Lemmas.TwoLineages
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.PositiveInitialExponent
import Probability.BranchingRandomWalk.Assumptions.Moments
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.FailureExpectation

import MeasureTheory.Integral.MeasurePreserving
import Combinatorics.UlamHarris.Order
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Upper expectation of the centered continuation

## Internal proof declarations

* `eventually_endpointMean_sub_horizon_le_of_firstMoment`: the upper mean
  bound holds uniformly for $H_N-i$, $0\le i\le T_N$, when
  $T_N=o(\log^3 N)$.

* `eventually_endpointMean_div_log_le_of_firstMoment`: if $0<a<1$ and
  $H_N/\log^3 N\to t>0$, the normalized endpoint mean from
  $\lfloor N^a\rfloor$ zero-position roots is eventually at most
  $-a+\pi^2\sigma^2t/2+\varepsilon$ for every $\varepsilon>0$.
  This uses the positive-exponent upper tail of Wang Yiyang,
  *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
  (Fudan University, 2026), Theorem 1.1, and two independent lineages to
  control the tail integral under the leftmost first-moment assumption.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

set_option maxHeartbeats 1200000 in
lemma eventually_endpointMean_div_log_le_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hne : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) (hε : 0 < ε)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    ∀ᶠ n in atTop,
      (∫ field, @countableRootEndpointMinimum (m n) (N n) (H n)
        (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / Real.log (N n : ℝ) ∂P) ≤
        -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε := by
  intro P m
  let μ := L.sortedPotentialImage
  let logN n := Real.log (N n : ℝ)
  let I n := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
  let F n := @countableRootEndpointMinimum (m n) (N n) (H n) (I n)
  let Y n ω := max (F n ω) 0
  let z := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε / 2
  let A n := {ω | z * logN n ≤ F n ω}
  let c := ∫ ξ, |value' ξ 0| ∂μ
  have hc : 0 ≤ c := integral_nonneg fun _ => abs_nonneg _
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hlog : Tendsto logN atTop atTop := Real.tendsto_log_atTop.comp hNr
  have hz : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < z := by dsimp [z]; linarith
  obtain ⟨b, hb, htprob⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent hN μ
      (L.sortedPotentialImage_hasBoundaryNormalization hboundary)
      (L.sortedPotentialImage_hasFiniteCrossWeight hboundary hcross) hsigma hspine ha ha1 ht hz hH I
  have hprob : ∀ᶠ n in atTop, P.real (A n) ≤ Real.exp (-b * logN n) := by
    filter_upwards [htprob] with n hn
    change P (A n) ≤ _ at hn
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hn
  have hsize : ∀ᶠ n in atTop, 2 ≤ m n ∧ 2 ≤ N n := by
    have hm := (tendsto_rpow_atTop ha).comp hNr
    filter_upwards [hm.eventually_ge_atTop 2, hN.eventually_ge_atTop 2] with n hm hn
    exact ⟨Nat.le_floor (by exact_mod_cast hm), hn⟩
  have hFm (n) : Measurable (F n) := by
    let := I n
    exact (measurable_firstNSelectedEndpointMinimum (m n) (N n) (H n)).comp
      (RootIndexed.StepField.measurePreserving_first μ (m n)).measurable
  have hFintegral : ∀ᶠ n in atTop, Integrable (F n) P := by
    filter_upwards [hsize] with n hn
    let := I n
    exact ((RootIndexed.StepField.measurePreserving_first μ (m n)).integrable_comp_of_integrable
      (finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum (m n) (N n) (H n)
        (by omega) (by omega) L hboundary hne hfirst))
  have hYbound : ∀ᶠ n in atTop, MemLp (Y n) 2 P ∧
      Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂P) ≤ (H n : ℝ) * c := by
    filter_upwards [hsize] with n hn
    let := I n
    obtain ⟨hint, hbound⟩ :=
      finiteRootStepFieldLaw_endpointMinimum_pos_sq_le L hboundary hne hfirst
        (m n) (N n) (H n) hn.1 hn.2
    let hpres := RootIndexed.StepField.measurePreserving_first μ (m n)
    have hintY : Integrable (fun ω => (Y n ω)^2) P := hpres.integrable_comp_of_integrable hint
    refine ⟨(memLp_two_iff_integrable_sq
      ((hFm n).max measurable_const).aestronglyMeasurable).2 hintY, ?_⟩
    have hident := hpres.integral_comp_of_integrable hint
    change (∫ ω, (Y n ω)^2 ∂P) = _ at hident
    rw [hident]
    exact (Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_sq (by positivity))
  have hYscale : ∀ᶠ n in atTop,
      Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂P) ≤ ((t + 1) * c) * logN n ^ 3 := by
    filter_upwards [hYbound, hlog.eventually_gt_atTop 0,
      hH.eventually (Iio_mem_nhds (lt_add_of_pos_right t one_pos))] with n hn hl hscale
    have hHn : (H n : ℝ) ≤ (t + 1) * logN n ^ 3 :=
      (div_le_iff₀ (pow_pos hl 3)).mp hscale.le
    exact hn.2.trans ((mul_le_mul_of_nonneg_right hHn hc).trans_eq (by ring))
  have htail := tendsto_setIntegral_div_log_of_failure P Y A (hYbound.mono fun _ h => h.1)
    hN (show 0 ≤ (t + 1) * c by positivity) hb hYscale hprob
  have hsmall : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n => -b * logN n) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith : -b < 0)).2 hlog
    exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hprob
      (Real.tendsto_exp_atBot.comp hneg)
  have herror := htail.add ((hsmall.const_mul (max (-z) 0)))
  simp only [mul_zero, add_zero] at herror
  filter_upwards [hFintegral, hYbound, hlog.eventually_gt_atTop 0,
    herror.eventually (Iio_mem_nhds (show 0 < ε / 2 by positivity))] with n hFn hYn hl hεn
  have hA : MeasurableSet (A n) := (hFm n) measurableSet_Ici
  have hYint : Integrable (Y n) P := hYn.1.integrable (by norm_num)
  have hsplit : (∫ ω, F n ω ∂P) ≤ z * logN n +
      (∫ ω in A n, Y n ω ∂P) + max (-z) 0 * logN n * P.real (A n) := by
    have hpoint (ω) : F n ω ≤ z * logN n +
        (A n).indicator (fun w => Y n w + max (-z) 0 * logN n) ω := by
      by_cases h : ω ∈ A n
      · rw [Set.indicator_of_mem h]
        have he := mul_nonneg (le_max_right (-z) 0) hl.le
        have hzge := mul_le_mul_of_nonneg_right (le_max_left (-z) 0) hl.le
        dsimp [Y]
        linarith [le_max_left (F n ω) 0]
      · rw [Set.indicator_of_notMem h]
        exact (lt_of_not_ge h).le.trans_eq (add_zero _).symm
    have hsum : Integrable (fun w => Y n w + max (-z) 0 * logN n) P :=
      hYint.add (integrable_const _)
    have hInt : Integrable (fun ω =>
        z * logN n + (A n).indicator (fun w => Y n w + max (-z) 0 * logN n) ω) P :=
      (integrable_const (z * logN n)).add (hsum.indicator hA)
    refine (integral_mono hFn hInt hpoint).trans_eq ?_
    rw [integral_add (f := fun _ => z * logN n) (integrable_const _) (hsum.indicator hA), integral_const,
      probReal_univ, one_smul, integral_indicator hA,
      integral_add hYint.integrableOn (integrable_const _), setIntegral_const, smul_eq_mul]
    ring
  rw [integral_div]
  apply (div_le_iff₀ hl).2
  have herr : (∫ ω in A n, Y n ω ∂P) + max (-z) 0 * logN n * P.real (A n) ≤
      ε / 2 * logN n := by
    have hn : (∫ ω in A n, Y n ω ∂P) / logN n +
        max (-z) 0 * P.real (A n) < ε / 2 := hεn
    apply le_of_lt
    convert (div_lt_iff₀ hl).mp (show
      ((∫ ω in A n, Y n ω ∂P) + max (-z) 0 * logN n * P.real (A n)) / logN n <
        ε / 2 from ?_) using 1
    rw [add_div]
    convert hn using 1
    field_simp
  dsimp [z] at hsplit
  linarith

/-- Uniform upper mean for deterministic horizons in the deadline window. -/
lemma eventually_endpointMean_sub_horizon_le_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
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
  obtain ⟨k, hk⟩ := (eventually_endpointMean_div_log_le_of_firstMoment L
    hnonempty hboundary hcross hfirst hsigma hspine ha ha1 ht (half_pos hε)
    (hN.comp hnTop) hremaining).exists
  exact (hbad k).not_ge (hk.trans (by dsimp [c]; linarith))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
