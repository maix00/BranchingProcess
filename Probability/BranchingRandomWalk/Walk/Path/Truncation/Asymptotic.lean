import Probability.BranchingRandomWalk.Walk.Path.Interpolation.MaximalJump
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Moment

/-!
# Asymptotics of truncated increments

This file turns the finite-cutoff estimates into statements along any cutoff
which tends to infinity.  The results depend only on the one-step law and
therefore remain in the random-walk path layer.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

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

/-- In particular, the truncation mean itself vanishes when the cutoff tends
to infinity. -/
theorem tendsto_abs_truncatedIncrementMean_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {radius : ℕ → ℝ} (hradius : Tendsto radius atTop atTop) :
    Tendsto (fun n => |truncatedIncrementMean ν (radius n)|)
      atTop (nhds 0) := by
  have hweighted := tendsto_radius_mul_abs_truncatedIncrementMean_zero
    ν hsq hcentered hradius
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => abs_nonneg _
  · filter_upwards [hradius.eventually (eventually_ge_atTop 1)] with n hn
    calc
      |truncatedIncrementMean ν (radius n)| =
          1 * |truncatedIncrementMean ν (radius n)| := by ring
      _ ≤ radius n * |truncatedIncrementMean ν (radius n)| :=
        mul_le_mul_of_nonneg_right hn (abs_nonneg _)
  · exact hweighted

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

/-- If the number of inspected coordinates is of order at most the square of
the truncation radius, then the union-bound contribution of discarded
increments vanishes.  The limit assumption is stated as convergence to an
arbitrary finite constant so that the result applies to both diffusive and
more general block parametrizations. -/
theorem tendsto_count_mul_measureReal_abs_ge_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {count : ℕ → ℕ} {radius : ℕ → ℝ} {ratioLimit : ℝ}
    (hradius : Tendsto radius atTop atTop)
    (hratio : Tendsto
      (fun n => (count n : ℝ) / radius n ^ 2)
      atTop (nhds ratioLimit)) :
    Tendsto (fun n => (count n : ℝ) * ν.real {x | radius n ≤ |x|})
      atTop (nhds 0) := by
  let tail : ℕ → ℝ := fun n =>
    ∫ x, {x | radius n ^ 2 ≤ x ^ 2}.indicator (fun x => x ^ 2) x ∂ν
  have htail : Tendsto tail atTop (nhds 0) := by
    have hradiusSq : Tendsto (fun n => radius n ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hradius
    exact tendsto_integral_indicator_threshold_le_zero hsq
      (fun x : ℝ => sq_nonneg x) _ hradiusSq
  have hproduct : Tendsto
      (fun n => ((count n : ℝ) / radius n ^ 2) * tail n)
      atTop (nhds 0) := by
    convert hratio.mul htail using 1
    simp
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  · filter_upwards [hradius.eventually (eventually_gt_atTop 0)] with n hn
    have hmarkov := sq_mul_measureReal_abs_ge_le_tailIntegral
      ν hsq (radius n) hn.le
    have hratioNonneg : 0 ≤ (count n : ℝ) / radius n ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    calc
      (count n : ℝ) * ν.real {x | radius n ≤ |x|} =
          ((count n : ℝ) / radius n ^ 2) *
            (radius n ^ 2 * ν.real {x | radius n ≤ |x|}) := by
              field_simp [hn.ne']
      _ ≤ ((count n : ℝ) / radius n ^ 2) * tail n :=
        mul_le_mul_of_nonneg_left hmarkov hratioNonneg
  · exact hproduct

/-- `ENNReal` form of the discarded-coordinate union cost, matching the
codomain of measure inequalities. -/
theorem tendsto_count_mul_measure_abs_ge_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {count : ℕ → ℕ} {radius : ℕ → ℝ} {ratioLimit : ℝ}
    (hradius : Tendsto radius atTop atTop)
    (hratio : Tendsto
      (fun n => (count n : ℝ) / radius n ^ 2)
      atTop (nhds ratioLimit)) :
    Tendsto (fun n => (count n : ENNReal) * ν {x | radius n ≤ |x|})
      atTop (nhds 0) := by
  have hreal := tendsto_count_mul_measureReal_abs_ge_zero
    ν hsq hradius hratio
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hofReal using 1
  · funext n
    change (count n : ENNReal) * ν {x | radius n ≤ |x|} =
      ENNReal.ofReal ((count n : ℝ) * ν.real {x | radius n ≤ |x|})
    symm
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg (count n)), ofReal_measureReal]
    simp
  · simp

/-- The accumulated centering error vanishes whenever its deterministic
coefficient, divided by `radius * threshold`, has a finite limit.  This is
the abstract bias-margin calculation used in truncated block estimates. -/
theorem tendsto_length_mul_abs_truncatedIncrementMean_div_threshold_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {length : ℕ → ℕ} {radius threshold : ℕ → ℝ} {ratioLimit : ℝ}
    (hradius : Tendsto radius atTop atTop)
    (hratio : Tendsto
      (fun n => ((length n + 1 : ℕ) : ℝ) /
        (radius n * threshold n))
      atTop (nhds ratioLimit))
    (hnonzero : ∀ᶠ n in atTop, radius n ≠ 0 ∧ threshold n ≠ 0) :
    Tendsto (fun n =>
        (((length n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (radius n)|) / threshold n)
      atTop (nhds 0) := by
  have hbias := tendsto_radius_mul_abs_truncatedIncrementMean_zero
    ν hsq hcentered hradius
  have hproduct := hratio.mul hbias
  have hproductZero : Tendsto
      (fun n => (((length n + 1 : ℕ) : ℝ) /
          (radius n * threshold n)) *
        (radius n * |truncatedIncrementMean ν (radius n)|))
      atTop (nhds 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  filter_upwards [hnonzero] with n hn
  rcases hn with ⟨hr, ht⟩
  field_simp [hr, ht]

end ProbabilityTheory.RandomWalk
