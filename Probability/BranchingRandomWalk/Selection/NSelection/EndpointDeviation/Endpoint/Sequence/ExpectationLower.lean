/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.FiniteVariance
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.FirstMoment
import MeasureTheory.Integral.MeasurePreserving
import Probability.MeasureTheory.Convergence.TailExpectation

/-!
# A lower limit for the mean selected endpoint

## Public declarations

* `le_liminf_integral_countableRootEndpointMinimum_div_log`:
  for the endpoint minimum $M_N$ from $N$ zero-position roots at capacity $N$,
  if $H_N/(\log N)^3\to t>0$, then
  $-1+\frac{\pi^2}{2}\sigma^2t\le\liminf_N \mathbb E[M_N]/\log N$.
  The endpoint is integrable under the leftmost first-moment assumption.

This is Lemma 4.1 of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4. The proof combines
the polynomial lower tail with $\mathbb E[e^{-M_N}]\le N$ and splits the
expectation at a threshold below the limiting value.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Lemma 4.1, Chapter 4 of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), on the common
root-field law for full-capacity starts. -/
theorem le_liminf_integral_countableRootEndpointMinimum_div_log
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ht : 0 < t) (H : ℕ → ℕ)
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin n) ℕ))
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    ((-1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t : ℝ) : EReal) ≤
      atTop.liminf (fun n : ℕ =>
        (((∫ field, @countableRootEndpointMinimum n n (H n) (horder n) field ∂P) /
          Real.log (n : ℝ) : ℝ) : EReal)) := by
  intro P
  let M := fun n => @countableRootEndpointMinimum n n (H n) (horder n)
  let X (n : ℕ) (field : CountableRootStepField ℕ ℝ) := if n = 0 then 0 else M n field
  let target := -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
  have hboundaryμ := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : L.sortedPotentialImage nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hmeas (n : ℕ) : Measurable (X n) := by
    let _ := horder n
    by_cases hn : n = 0
    · simpa only [X, ite_eq_left hn] using (measurable_const (a := (0 : ℝ)))
    · simpa only [X, ite_eq_right hn, M] using measurable_countableRootEndpointMinimum n n (H n)
  have hX (n : ℕ) : Integrable (X n) P := by
    let _ := horder n
    by_cases hn : 0 < n
    · have hfinite := finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
        n n (H n) hn hn L hboundary hnonempty hfirst
      have hpreserving := RootIndexed.StepField.measurePreserving_first L.sortedPotentialImage n
      simpa only [X, ite_eq_right hn.ne', M, countableRootEndpointMinimum, Function.comp_def] using
        hpreserving.integrable_comp_of_integrable hfinite
    · simp [X, Nat.eq_zero_of_not_pos hn]
  have hfiniteExp (n : ℕ) (hn : 0 < n) :
      Integrable (fun field => Real.exp
        (-@firstNSelectedEndpointMinimum n n (H n) (horder n) field))
        (finiteRootStepFieldLaw L.sortedPotentialImage n) := by
    let _ := horder n
    exact finiteRootStepFieldLaw_integrable_exp_neg_firstNSelectedEndpointMinimum
      n n (H n) hn hn L.sortedPotentialImage hboundaryμ hnonemptyμ
  have hExp (n : ℕ) : Integrable (fun field => Real.exp (-X n field)) P := by
    by_cases hn : 0 < n
    · have hpreserving := RootIndexed.StepField.measurePreserving_first L.sortedPotentialImage n
      simpa only [X, ite_eq_right hn.ne', M, countableRootEndpointMinimum, Function.comp_def] using
        hpreserving.integrable_comp_of_integrable (hfiniteExp n hn)
    · simp [X, Nat.eq_zero_of_not_pos hn]
  have hExpBound : ∀ᶠ n : ℕ in atTop, (∫ field, Real.exp (-X n field) ∂P) ≤ (n : ℝ) := by
    filter_upwards [hpos] with n hn
    let _ := horder n
    have hbound := finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
      n n (H n) hn hn L.sortedPotentialImage hboundaryμ hnonemptyμ
    rw [← ofReal_integral_eq_lintegral_ofReal (hfiniteExp n hn)
      (Eventually.of_forall fun _ => Real.exp_nonneg _)] at hbound
    have hboundReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.exp_nonneg _),
      ENNReal.toReal_ofReal (Nat.cast_nonneg n)] at hboundReal
    have hpreserving := RootIndexed.StepField.measurePreserving_first L.sortedPotentialImage n
    simpa only [X, ite_eq_right hn.ne', M, countableRootEndpointMinimum, Function.comp_def] using
      (hpreserving.integral_comp_of_integrable (hfiniteExp n hn)).le.trans hboundReal
  refine (target_le_liminf_integral_div_log_of_polynomial_lower_tail
    (fun _ => P) (fun _ => inferInstance) X target hmeas hX hExp hExpBound ?_).trans_eq ?_
  · intro z hz
    have hscale : Tendsto (fun n : ℕ => z * Real.log (n : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 z) := by
      apply tendsto_const_nhds.congr'
      have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hlog.eventually_gt_atTop 0] with n hn
      exact (mul_div_cancel_right₀ _ hn.ne').symm
    let _ := tiltedPotentialLaw_isProbability realPotential L.sortedPotentialImage hboundaryμ
    obtain ⟨ε, hε, htail⟩ :=
      eventually_countableRootEndpointMinimum_le_polynomial_of_centeredFiniteVariance
        L.sortedPotentialImage hboundaryμ hnonemptyμ _ rfl hsigma hspine (a := 1)
        horder tendsto_id hH hscale ht zero_le_one
        (Eventually.of_forall fun _ => le_rfl) hpos
        (Eventually.of_forall fun n => by simp [Real.rpow_one]) hz
    refine ⟨ε, hε, ?_⟩
    filter_upwards [htail, hpos] with n htailN hn
    have hnorm : Real.exp (-ε * Real.log (n : ℝ)) = 1 / (n : ℝ) ^ ε := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hn), one_div, ← Real.exp_neg]
      congr 1
      ring
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htailN
    simp only [id_eq, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
    simpa only [X, ite_eq_right hn.ne', M, Measure.real, hnorm] using hreal
  · apply liminf_congr
    filter_upwards [hpos] with n hn
    simp only [X, ite_eq_right hn.ne', M]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
