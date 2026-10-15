/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Normal
public import Probability.Distributions.Gaussian.Sign
public import Probability.Distributions.Moments.Real
public import Probability.ConvergenceInDistribution.Portmanteau
public import Algebra.BigOperators.AdditivePath

/-!
# The positivity parameter of a finite-variance random walk

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.tendsto_positivePartialSumProbability_half`:
  for centered increments with variance $\sigma^2>0$,
  $\mathbb P(S_n>0)\to 1/2$.

This is the Gaussian positivity-parameter input to R. A. Doney,
*Spitzer's condition and ladder variables in random walks*, Theorem 2
(Probab. Theory Relat. Fields 101 (1995), 577--580), which is one of the
ladder-variable results cited in Francesco Caravenna and Loïc Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
Lemma 2.1 (Ann. Inst. H. Poincaré Probab. Statist. 44 (2008), 170--190).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ProbabilityTheory.RandomWalk

/-- The centered finite-variance walk has Gaussian positivity parameter
$\rho=1/2$. The event is stated directly in terms of the partial sum. -/
theorem tendsto_positivePartialSumProbability_half
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    Tendsto (fun n : ℕ => iidSequenceLaw ν
      {increment | 0 < AdditivePath.displacement n increment})
      atTop (nhds ((1 / 2 : ℝ≥0∞))) := by
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (by
      rw [hν.2]
      exact pow_ne_zero 2 hsigma.ne')
  let scale : ℕ → ℝ :=
    fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)
  have hnormal :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hν.1 hsquare (hν.2 ▸ sq_pos_of_pos hsigma)
  have hzero : (gaussianReal 0 (1 : ℝ≥0))
      (frontier (Set.Ioi (0 : ℝ))) = 0 := by
    rw [frontier_Ioi]
    exact @measure_singleton ℝ _ (gaussianReal 0 (1 : ℝ≥0))
      (nullSingletonClass_gaussianReal (by norm_num)) 0
  have hlimit := hnormal.tendstoInDistribution.tendsto_measure_map_of_null_frontier
    (by simpa only [Measure.map_id] using hzero)
  have heq :
      (fun n : ℕ => (iidSequenceLaw ν).map
        (normalizedIidSum scale (fun _ => 0) n) (Set.Ioi 0)) =ᶠ[atTop]
      (fun n : ℕ => iidSequenceLaw ν
        {increment | 0 < AdditivePath.displacement n increment}) := by
    filter_upwards [hnormal.eventually_scale_pos] with n hn
    rw [Measure.map_apply (normalizedIidSum_measurable _ _ _)
      measurableSet_Ioi]
    congr 1
    ext increment
    change 0 < (scale n)⁻¹ *
      ((∑ k ∈ Finset.range n, increment k) - 0) ↔
      0 < AdditivePath.displacement n increment
    simpa [AdditivePath.displacement] using
      (mul_pos_iff_of_pos_left (inv_pos.mpr hn) :
        0 < (scale n)⁻¹ * (∑ k ∈ Finset.range n, increment k) ↔
          0 < ∑ k ∈ Finset.range n, increment k)
  have hpositive : (gaussianReal 0 (1 : ℝ≥0)) (Set.Ioi 0) =
      (1 / 2 : ℝ≥0∞) := by
    have hsym : (gaussianReal 0 (1 : ℝ≥0)) (Set.Ioi 0) =
        (gaussianReal 0 (1 : ℝ≥0)) (Set.Iio 0) := by
      have hmap := gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      calc
        (gaussianReal 0 (1 : ℝ≥0)) (Set.Ioi 0) =
            ((gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => -x))
              (Set.Ioi 0) := by
          simpa using congrArg (fun μ : Measure ℝ => μ (Set.Ioi 0)) hmap.symm
        _ = (gaussianReal 0 (1 : ℝ≥0)) (Set.Iio 0) := by
          rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
          congr 1
          ext x
          simp
    have hhalf := gaussianReal_Iio_zero_two_mul (by norm_num :
      (0 : ℝ≥0) < 1)
    rw [← hsym] at hhalf
    calc
      (gaussianReal 0 (1 : ℝ≥0)) (Set.Ioi 0) =
          (2 : ℝ≥0∞)⁻¹ *
            (2 * (gaussianReal 0 (1 : ℝ≥0)) (Set.Ioi 0)) := by
              exact (ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)).symm
      _ = (2 : ℝ≥0∞)⁻¹ * 1 := congrArg _ hhalf
      _ = 1 / 2 := by norm_num
  have hlimit' : Tendsto
      (fun n : ℕ => (iidSequenceLaw ν).map
        (normalizedIidSum scale (fun _ => 0) n) (Set.Ioi 0))
      atTop (nhds (1 / 2 : ℝ≥0∞)) := by
    simpa only [Measure.map_id, hpositive] using hlimit
  exact hlimit'.congr' heq

end ProbabilityTheory.RandomWalk

end
