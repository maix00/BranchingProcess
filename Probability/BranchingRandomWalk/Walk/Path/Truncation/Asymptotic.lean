import Probability.BranchingRandomWalk.Walk.Path.Interpolation.MaximalJump
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Moment

/-!
# Asymptotics of truncated increments

This file turns the finite-cutoff estimates into statements along any cutoff
which tends to infinity.  The results depend only on the one-step law and
therefore remain in the random-walk path layer.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- The discarded second moment vanishes along every truncation radius tending
to infinity. -/
theorem tendsto_integral_tail_sq_zero
    {ν : Measure ℝ} (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℕ → ℝ} (hradius : Tendsto radius atTop atTop) :
    Tendsto (fun n =>
        ∫ x, {y : ℝ | radius n < |y|}.indicator (fun y => y ^ 2) x ∂ν)
      atTop (nhds 0) := by
  let upper : ℕ → ℝ := fun n =>
    ∫ x, {y : ℝ | radius n ^ 2 ≤ y ^ 2}.indicator (fun y => y ^ 2) x ∂ν
  have hradiusSq : Tendsto (fun n => radius n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hradius
  have hupper : Tendsto upper atTop (nhds 0) :=
    tendsto_integral_indicator_threshold_le_zero hsq
      (fun x : ℝ => sq_nonneg x) _ hradiusSq
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => integral_nonneg fun x => by
      exact Set.indicator_nonneg (fun y _ => sq_nonneg y) x
  · filter_upwards [hradius.eventually (eventually_ge_atTop 0)] with n hn
    let tail : Set ℝ := {y | radius n < |y|}
    let closedTail : Set ℝ := {y | radius n ^ 2 ≤ y ^ 2}
    have htail : MeasurableSet tail :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hclosedTail : MeasurableSet closedTail :=
      measurableSet_le measurable_const (measurable_id.pow_const 2)
    have htailInt : Integrable (tail.indicator fun y : ℝ => y ^ 2) ν :=
      hsq.indicator htail
    have hclosedTailInt :
        Integrable (closedTail.indicator fun y : ℝ => y ^ 2) ν :=
      hsq.indicator hclosedTail
    change (∫ x, tail.indicator (fun y => y ^ 2) x ∂ν) ≤ upper n
    change (∫ x, tail.indicator (fun y => y ^ 2) x ∂ν) ≤
      ∫ x, closedTail.indicator (fun y => y ^ 2) x ∂ν
    refine integral_mono htailInt hclosedTailInt ?_
    intro x
    by_cases hx : x ∈ tail
    · rw [Set.indicator_of_mem hx,
          Set.indicator_of_mem (show x ∈ closedTail by
            change radius n ^ 2 ≤ x ^ 2
            rw [sq_le_sq, abs_of_nonneg hn]
            exact (show radius n < |x| from hx).le)]
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun y _ => sq_nonneg y) x
  · exact hupper

/-- For centered finite-variance increments, the cutoff times the truncation
bias tends to zero along every cutoff tending to infinity. -/
theorem tendsto_radius_mul_abs_truncatedIncrementMean_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {radius : ℕ → ℝ} (hradius : Tendsto radius atTop atTop) :
    Tendsto (fun n => radius n * |truncatedIncrementMean ν (radius n)|)
      atTop (nhds 0) := by
  have htail := tendsto_integral_tail_sq_zero hsq hradius
  apply squeeze_zero'
  · filter_upwards [hradius.eventually (eventually_ge_atTop 0)] with n hn
    exact mul_nonneg hn (abs_nonneg _)
  · filter_upwards [hradius.eventually (eventually_ge_atTop 0)] with n hn
    exact radius_mul_abs_truncatedIncrementMean_le_integral_tail_sq
      ν hsq hcentered hn
  · exact htail

/-- Fourth-power form of the vanishing truncation-bias estimate. -/
theorem tendsto_radius_pow_four_mul_truncatedIncrementMean_pow_four_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {radius : ℕ → ℝ} (hradius : Tendsto radius atTop atTop) :
    Tendsto (fun n => radius n ^ 4 *
        truncatedIncrementMean ν (radius n) ^ 4) atTop (nhds 0) := by
  have h := (tendsto_radius_mul_abs_truncatedIncrementMean_zero
    ν hsq hcentered hradius).pow 4
  convert h using 1
  · funext n
    rw [mul_pow]
    congr 1
    calc
      truncatedIncrementMean ν (radius n) ^ 4 =
          (truncatedIncrementMean ν (radius n) ^ 2) ^ 2 := by ring
      _ = (|truncatedIncrementMean ν (radius n)| ^ 2) ^ 2 := by
        rw [sq_abs]
      _ = |truncatedIncrementMean ν (radius n)| ^ 4 := by ring
  · norm_num

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
