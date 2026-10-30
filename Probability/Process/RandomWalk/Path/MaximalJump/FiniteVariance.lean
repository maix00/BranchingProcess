/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Integral.Convergence.IndicatorTail
public import MeasureTheory.Measure.Tails.SecondMoment
public import Probability.Process.RandomWalk.Path.MaximalJump.Basic
public import Probability.Sequence.IID.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite-variance maximal-increment estimates

For IID real increments with a finite second moment, this module proves a
union-bound estimate for the largest increment and its negligibility on the
diffusive scale.

## Public declarations

* `ProbabilityTheory.RandomWalk.iidSequenceLaw_maxAbsUpTo_ge_le` gives the
  union bound for the largest increment among indices $0,\ldots,n$.
* `ProbabilityTheory.RandomWalk.sq_mul_iidSequenceLaw_maxAbsUpTo_ge_le`
  bounds this tail by the integrated second-moment tail.
* `ProbabilityTheory.RandomWalk.tendsto_measureReal_maxAbsUpTo_ge_mul_sqrt_zero`
  and `tendstoInMeasure_invSqrt_mul_maxAbsUpTo_zero` show that the maximum
  increment is negligible at diffusive scale.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The probability that one of the first `n + 1` IID increments exceeds a
threshold is at most `(n + 1)` times the corresponding one-step tail
probability. -/
theorem iidSequenceLaw_maxAbsUpTo_ge_le
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (threshold : ℝ) :
    (iidSequenceLaw nu).real
        {increment | threshold ≤ maxAbsUpTo n increment} ≤
      (n + 1 : ℝ) * nu.real {x | threshold ≤ |x|} := by
  let event : ℕ → Set (ℕ → ℝ) :=
    fun k => {increment | threshold ≤ |increment k|}
  have hevent :
      {increment | threshold ≤ maxAbsUpTo n increment} =
        ⋃ k ∈ Finset.range (n + 1), event k := by
    ext increment
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, event]
    unfold maxAbsUpTo
    rw [Finset.le_sup'_iff]
    simp only [Finset.mem_range]
    aesop
  rw [hevent]
  refine (measureReal_biUnion_finset_le (Finset.range (n + 1)) event).trans ?_
  have hcoordinate (k : ℕ) :
      (iidSequenceLaw nu).real (event k) =
        nu.real {x | threshold ≤ |x|} := by
    have hset : MeasurableSet {x : ℝ | threshold ≤ |x|} :=
      measurableSet_Ici.preimage measurable_abs
    change (iidSequenceLaw nu).real
        ((fun increment : ℕ → ℝ => increment k) ⁻¹' {x | threshold ≤ |x|}) = _
    apply congrArg ENNReal.toReal
    calc
      iidSequenceLaw nu
          ((fun increment : ℕ → ℝ => increment k) ⁻¹' {x | threshold ≤ |x|}) =
          (iidSequenceLaw nu).map
            (fun increment => increment k) {x | threshold ≤ |x|} :=
        (Measure.map_apply (measurable_pi_apply k) hset).symm
      _ = nu {x | threshold ≤ |x|} := by
        rw [iidSequenceLaw_map_apply nu k]
  simp_rw [hcoordinate]
  simp [Nat.cast_add, Nat.cast_one]

/-- A maximal-increment estimate with a vanishing second-moment tail on the
right.  This is the quantitative input for the interpolation comparison. -/
theorem sq_mul_iidSequenceLaw_maxAbsUpTo_ge_le
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    (n : ℕ) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    threshold ^ 2 * (iidSequenceLaw nu).real
        {increment | threshold ≤ maxAbsUpTo n increment} ≤
      (n + 1 : ℝ) *
        ∫ x, {x | threshold ^ 2 ≤ x ^ 2}.indicator (fun x => x ^ 2) x ∂nu := by
  have hmax := iidSequenceLaw_maxAbsUpTo_ge_le nu n threshold
  have htail := sq_mul_measureReal_abs_ge_le_tailIntegral
    nu hsq threshold hthreshold
  calc
    threshold ^ 2 * (iidSequenceLaw nu).real
        {increment | threshold ≤ maxAbsUpTo n increment} ≤
        threshold ^ 2 * ((n + 1 : ℝ) *
          nu.real {x | threshold ≤ |x|}) :=
      mul_le_mul_of_nonneg_left hmax (sq_nonneg threshold)
    _ = (n + 1 : ℝ) *
        (threshold ^ 2 * nu.real {x | threshold ≤ |x|}) := by ring
    _ ≤ (n + 1 : ℝ) *
        ∫ x, {x | threshold ^ 2 ≤ x ^ 2}.indicator (fun x => x ^ 2) x ∂nu :=
      mul_le_mul_of_nonneg_left htail (by positivity)

/-- Under a finite second moment, the largest of the first `n + 1`
increments is negligible on the diffusive scale. -/
theorem tendsto_measureReal_maxAbsUpTo_ge_mul_sqrt_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (iidSequenceLaw nu).real
        {increment | epsilon * Real.sqrt n ≤ maxAbsUpTo n increment})
      atTop (nhds 0) := by
  let tail : ℕ → ℝ := fun n =>
    ∫ x, {x | (epsilon * Real.sqrt n) ^ 2 ≤ x ^ 2}.indicator
      (fun x => x ^ 2) x ∂nu
  have hthreshold : Tendsto (fun n : ℕ => epsilon ^ 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (sq_pos_of_pos hepsilon)
  have htail : Tendsto tail atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_integral_indicator_of_threshold_tendsto_atTop hsq
      (fun x : ℝ => sq_nonneg x) _ hthreshold
    apply h.congr'
    filter_upwards [] with n
    unfold tail
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ => (n + 1 : ℝ) / ((epsilon * Real.sqrt n) ^ 2))
      atTop (nhds ((epsilon ^ 2)⁻¹)) := by
    have hbase : Tendsto (fun n : ℕ => 1 + ((n : ℝ))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    have hdiv := hbase.div_const (epsilon ^ 2)
    have hratio' : Tendsto
        (fun n : ℕ => (n + 1 : ℝ) / ((epsilon * Real.sqrt n) ^ 2))
        atTop (nhds (1 / epsilon ^ 2)) := by
      apply hdiv.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp [hepsilon.ne', hn.ne']
    simpa [one_div] using hratio'
  have hupper : Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℝ) * tail n) / ((epsilon * Real.sqrt n) ^ 2))
      atTop (nhds 0) := by
    have hproduct : Tendsto
        (fun n : ℕ => ((n + 1 : ℝ) / ((epsilon * Real.sqrt n) ^ 2)) * tail n)
        atTop (nhds 0) := by
      simpa using hratio.mul htail
    apply hproduct.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    field_simp [hepsilon.ne', hsqrt.ne']
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => measureReal_nonneg
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    exact (le_div_iff₀' (sq_pos_of_pos (mul_pos hepsilon hsqrt))).2
      (sq_mul_iidSequenceLaw_maxAbsUpTo_ge_le
        nu hsq n (epsilon * Real.sqrt n) (mul_nonneg hepsilon.le hsqrt.le))
  · exact hupper

/-- The normalized maximal increment converges to zero in probability. -/
theorem tendstoInMeasure_invSqrt_mul_maxAbsUpTo_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu) :
    TendstoInMeasure (iidSequenceLaw nu)
      (fun (n : ℕ) increment => (Real.sqrt n)⁻¹ * maxAbsUpTo n increment)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have htail := tendsto_measureReal_maxAbsUpTo_ge_mul_sqrt_zero
    nu hsq hepsilon
  apply htail.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext increment
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hmax : 0 ≤ maxAbsUpTo n increment := maxAbsUpTo_nonneg n increment
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul,
    abs_inv, abs_of_pos hsqrt, abs_of_nonneg hmax]
  rw [le_inv_mul_iff₀ hsqrt]
  simp only [mul_comm]


end ProbabilityTheory.RandomWalk
