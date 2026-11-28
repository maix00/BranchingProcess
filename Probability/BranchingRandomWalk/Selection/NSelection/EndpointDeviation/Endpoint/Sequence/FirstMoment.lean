/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.FullCapacity
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.FiniteVariance
public import Probability.BranchingRandomWalk.Step.Ordering.Spine
public import Probability.BranchingRandomWalk.Assumptions.Moments
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Lemmas.TwoLineages
import Probability.MeasureTheory.Convergence.FirstMoment.FromTails
import MeasureTheory.Integral.Convergence.ExceptionalEvent
import MeasureTheory.Integral.MeasurePreserving

/-!
# Endpoint first-moment limits under the weak reproductive tail

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_eLpNorm_one_countableRootEndpointMinimum_div_sub_of_spinalWeightTail`:
  for `0<a≤1`, `H_n/log³N_n→t>0`, boundary normalization, nonempty
  offspring, weak spinal reproductive tails, centered variance `σ²>0`
  and `E[Y⁺]<∞` for the leftmost child, the actual endpoint from
  `⌊N_n^a⌋` zero-position roots satisfies
  `‖M_n/log N_n-(-a+π²σ²t/2)‖₁→0`.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_integral_countableRootEndpointMinimum_div_of_spinalWeightTail`:
  under the same assumptions, `E[M_n/log N_n]→-a+π²σ²t/2`.

The positive-tail expectation is bounded by two independent lineages, using
only the first moment of the leftmost child. Negative tails use the original
exponential weight bound. The generic first-moment convergence criterion
then completes the limit without finite cross weight or a fourth moment.
This is the weak-tail strengthening of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1, using B. Mallein, *N-branching random walk with
α-stable spine*, Theorem 1.1 condition (1.9), arXiv:1503.03762v2.
-/

@[expose] public section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000 in
private lemma eventually_endpointMean_div_log_le_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hne : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 < t) (hε : 0 < ε)
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
  have hneμ : μ nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hne]
  obtain ⟨b, hb, htprob⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_of_positiveExponent hN μ
      (L.sortedPotentialImage_hasBoundaryNormalization hboundary) hneμ
      (L.sortedPotentialImage_hasSpinalWeightTail_iff.mpr htail) hsigma hspine ha ha1 ht hH hz
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
  have htail := tendsto_setIntegral_div_of_polynomial_second_moment_and_exponential_probability
    P Y A hlog (hYbound.mono fun _ h => h.1)
    (show 0 ≤ (t + 1) * c by positivity) hb
    (r := 3) (by simpa only [Real.rpow_ofNat] using hYscale) hprob
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


/-- The weak-tail `L¹` strengthening of Wang Yiyang, Chapter 4, Theorem 1.1,
for all positive initial exponents including full capacity. Only `E[Y⁺]`
is assumed for the leftmost child; the reproductive assumption is precisely
Mallein's Theorem 1.1 (1.9), arXiv:1503.03762v2. -/
theorem tendsto_eLpNorm_one_countableRootEndpointMinimum_div_sub_of_spinalWeightTail
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 < t)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    let endpoint n := @countableRootEndpointMinimum (m n) (N n) (H n)
      (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
    let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => eLpNorm (fun field => endpoint n field / Real.log (N n : ℝ) - c)
      1 P) atTop (𝓝 0) := by
  intro P m F c
  let μ := L.sortedPotentialImage
  let ℓ n := Real.log (N n : ℝ)
  have hb := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hne : μ nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hℓ : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hN)
  have hsize : ∀ᶠ n in atTop, 0 < m n ∧ 0 < N n ∧ m n ≤ N n := by
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    have hNr : (1 : ℝ) ≤ N n := by exact_mod_cast hn
    have hmr : (m n : ℝ) ≤ (N n : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow hNr ha.le), by omega, ?_⟩
    have hle := Real.rpow_le_rpow_of_exponent_le hNr ha1
    rw [Real.rpow_one] at hle
    exact_mod_cast hmr.trans hle
  have hInt : ∀ᶠ n in atTop, Integrable (F n) P := by
    filter_upwards [hsize] with n hn
    let := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    exact (RootIndexed.StepField.measurePreserving_first μ (m n)).integrable_comp_of_integrable
      (finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum (m n) (N n) (H n)
        hn.1 hn.2.1 L hboundary hnonempty hfirst)
  have hExp : ∀ᶠ n in atTop, Integrable (fun field => Real.exp (-F n field)) P := by
    filter_upwards [hsize] with n hn
    let := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    exact (RootIndexed.StepField.measurePreserving_first μ (m n)).integrable_comp_of_integrable
      (finiteRootStepFieldLaw_integrable_exp_neg_firstNSelectedEndpointMinimum
        (m n) (N n) (H n) hn.1 hn.2.1 μ hb hne)
  have hExpBound : ∀ᶠ n in atTop, (∫ field, Real.exp (-F n field) ∂P) ≤ Real.exp (1 * ℓ n) := by
    filter_upwards [hsize, hExp] with n hn he
    let := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    have hbound := finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
      (m n) (N n) (H n) hn.1 hn.2.1 μ hb hne
    have hmap := (RootIndexed.StepField.measurePreserving_first μ (m n)).lintegral_comp
      (f := fun field => ENNReal.ofReal (Real.exp
        (-firstNSelectedEndpointMinimum (m n) (N n) (H n) field)))
      (by exact ((measurable_firstNSelectedEndpointMinimum (m n) (N n) (H n)).neg.exp).ennreal_ofReal)
    have hb' : (∫⁻ field, ENNReal.ofReal (Real.exp (-F n field)) ∂P) ≤ (m n : ℝ≥0∞) := by
      change (∫⁻ field, ENNReal.ofReal (Real.exp
        (-firstNSelectedEndpointMinimum (m n) (N n) (H n)
          (RootIndexed.StepField.first (m n) field))) ∂P) ≤ _
      change (∫⁻ field, ENNReal.ofReal (Real.exp
        (-firstNSelectedEndpointMinimum (m n) (N n) (H n)
          (RootIndexed.StepField.first (m n) field))) ∂RootIndexed.stepFieldLaw μ) ≤ _
      rw [hmap]
      simpa only [ENNReal.ofReal_natCast] using hbound
    rw [← ofReal_integral_eq_lintegral_ofReal he
      (Eventually.of_forall fun _ => Real.exp_nonneg _)] at hb'
    have hr := ENNReal.toReal_mono (ENNReal.natCast_ne_top (m n)) hb'
    simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.exp_nonneg _),
      ENNReal.toReal_natCast] at hr
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hn.2.1
    rw [one_mul, Real.exp_log hNr]
    exact hr.trans (by exact_mod_cast hn.2.2)
  let : IsProbabilityMeasure (tiltedPotentialLaw realPotential (-1) μ) :=
    tiltedPotentialLaw_isProbability realPotential μ hb
  apply tendsto_eLpNorm_one_div_sub_of_lower_tails_and_upper_mean
    (fun _ => P) (fun _ => inferInstance) F hℓ
    (fun n => measurable_countableRootEndpointMinimum (m n) (N n) (H n)) hInt hExp hExpBound
  · intro z hz
    have hscale : Tendsto (fun n => z * ℓ n / ℓ n) atTop (𝓝 z) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hℓ.eventually_gt_atTop 0] with n hn
      exact (mul_div_cancel_right₀ _ hn.ne').symm
    obtain ⟨p, hp, hprob⟩ :=
      eventually_countableRootEndpointMinimum_le_polynomial_of_centeredFiniteVariance μ hb hne
        _ rfl hsigma hspine (fun n => RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
        hN hH hscale ht ha.le (hsize.mono fun _ h => h.2.2) (hsize.mono fun _ h => h.1)
        (Eventually.of_forall fun n => Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hz
    refine ⟨p, hp, ?_⟩
    filter_upwards [hprob] with n hn
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hn
  · intro ε hε
    exact eventually_endpointMean_div_log_le_of_firstMoment L hnonempty hboundary htail hfirst
      hsigma hspine ha ha1 ht hε hN hH

/-- Expectation convergence follows from the same `L¹` endpoint theorem
by native continuity of the Bochner integral, without a second proof of
uniform integrability. -/
theorem tendsto_integral_countableRootEndpointMinimum_div_of_spinalWeightTail
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 < t)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    let endpoint n := @countableRootEndpointMinimum (m n) (N n) (H n)
      (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
    let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => ∫ field, endpoint n field / Real.log (N n : ℝ) ∂P)
      atTop (𝓝 c) := by
  intro P m F c
  have hL1 := tendsto_eLpNorm_one_countableRootEndpointMinimum_div_sub_of_spinalWeightTail L
    hnonempty hboundary htail hfirst hsigma hspine ha ha1 ht hN hH
  have hInt : ∀ᶠ n in atTop, Integrable (fun field => F n field / Real.log (N n : ℝ)) P := by
    have hfinite := hL1.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < ∞ by simp))
    filter_upwards [hfinite] with n hn
    have hi : Integrable (fun field => F n field / Real.log (N n : ℝ) - c) P :=
      memLp_one_iff_integrable.mp hn
    convert hi.add (integrable_const c) using 1
    ext field
    change F n field / Real.log (N n : ℝ) = (F n field / Real.log (N n : ℝ) - c) + c
    ring
  simpa using tendsto_integral_of_L1' (fun _ => c) hInt hL1

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
