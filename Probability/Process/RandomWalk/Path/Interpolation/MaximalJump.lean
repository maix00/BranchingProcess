/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Maximal increments of an IID walk

This file contains the probability estimates needed to compare the step and
polygonal realizations of a random walk.  The estimates concern only the
increment process; the deterministic interpolation bound remains in the
combinatorial layer.
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

/-- The part of an integrable nonnegative function above a threshold tending
to infinity has integral tending to zero. -/
theorem tendsto_integral_indicator_threshold_le_zero
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : Integrable f mu) (hf_nonneg : 0 ≤ f)
    (threshold : ℕ → ℝ) (hthreshold : Tendsto threshold atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x, {x | threshold n ≤ f x}.indicator f x ∂mu)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) :
      AEStronglyMeasurable ({x | threshold n ≤ f x}.indicator f) mu := by
    exact hf.aestronglyMeasurable.indicator₀
      (hf.aemeasurable.nullMeasurable measurableSet_Ici)
  have hbound (n : ℕ) : ∀ᵐ x ∂mu,
      ‖{x | threshold n ≤ f x}.indicator f x‖ ≤ f x := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    by_cases hx : threshold n ≤ f x
    · rw [Set.indicator_of_mem (show x ∈ {y | threshold n ≤ f y} from hx),
        abs_of_nonneg (hf_nonneg x)]
    · rw [Set.indicator_of_notMem
          (show x ∉ {y | threshold n ≤ f y} from hx), abs_zero]
      exact hf_nonneg x
  have hlim : ∀ᵐ x ∂mu,
      Tendsto (fun n : ℕ => {x | threshold n ≤ f x}.indicator f x)
        atTop (nhds 0) := by
    filter_upwards [] with x
    have heventually' : ∀ᶠ n in atTop, f x + 1 ≤ threshold n :=
      tendsto_atTop.1 hthreshold (f x + 1)
    have heventually : ∀ᶠ n in atTop, f x < threshold n := by
      filter_upwards [heventually'] with n hn
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards [heventually] with n hn
    rw [Set.indicator_of_notMem]
    exact not_le_of_gt hn
  simpa using (tendsto_integral_of_dominated_convergence
    (f := fun _ : X => 0) f hmeas hf hbound hlim)

/-- Natural-number thresholds are a useful special case of the preceding
tail-integral lemma. -/
theorem tendsto_integral_indicator_nat_le_zero
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : Integrable f mu) (hf_nonneg : 0 ≤ f) :
    Tendsto (fun n : ℕ => ∫ x, {x | (n : ℝ) ≤ f x}.indicator f x ∂mu)
      atTop (nhds 0) :=
  tendsto_integral_indicator_threshold_le_zero hf hf_nonneg
    (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop

/-- Markov's inequality localized to the tail event.  Unlike the usual
form, its right-hand side is the tail integral and therefore vanishes as the
threshold tends to infinity. -/
theorem mul_measureReal_le_integral_indicator
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : Integrable f mu) (hf_nonneg : 0 ≤ f)
    (hf_meas : StronglyMeasurable f) (threshold : ℝ) :
    threshold * mu.real {x | threshold ≤ f x} ≤
      ∫ x, {x | threshold ≤ f x}.indicator f x ∂mu := by
  let tail : Set X := {x | threshold ≤ f x}
  have htail : MeasurableSet tail :=
    measurableSet_Ici.preimage hf_meas.measurable
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := mu.restrict tail) (f := f)
    (ae_restrict_of_forall_mem htail fun x _ => hf_nonneg x)
    (hf.mono_measure Measure.restrict_le_self) threshold
  change threshold * mu.real tail ≤ ∫ x, tail.indicator f x ∂mu
  rw [integral_indicator htail]
  change threshold * (mu.restrict tail).real tail ≤
    ∫ x in tail, f x ∂mu at hmarkov
  simpa only [Measure.real, Measure.restrict_apply htail,
    Set.inter_self] using hmarkov

/-- The second-moment tail inequality in the form used for maximal jumps. -/
theorem sq_mul_measureReal_abs_ge_le_tailIntegral
    (nu : Measure ℝ) (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    threshold ^ 2 * nu.real {x | threshold ≤ |x|} ≤
      ∫ x, {x | threshold ^ 2 ≤ x ^ 2}.indicator (fun x => x ^ 2) x ∂nu := by
  have h := mul_measureReal_le_integral_indicator hsq
    (fun x => sq_nonneg x) (by fun_prop) (threshold ^ 2)
  have hset : {x : ℝ | threshold ^ 2 ≤ x ^ 2} =
      {x | threshold ≤ |x|} := by
    ext x
    simpa only [Set.mem_ofPred_eq, sq_abs] using
      (sq_le_sq₀ hthreshold (abs_nonneg x))
  rw [← hset]
  exact h

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
    have h := tendsto_integral_indicator_threshold_le_zero hsq
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

/-- The step and polygonal realizations of a finite-second-moment walk are
asymptotically equivalent in the Skorokhod `J₁` metric. -/
theorem tendsto_measureReal_edist_normalizedStepPath_linear_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (iidSequenceLaw nu).real
        {increment | ENNReal.ofReal epsilon ≤
          edist
            (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
            (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment)})
      atTop (nhds 0) := by
  have hmax := tendsto_measureReal_maxAbsUpTo_ge_mul_sqrt_zero
    nu hsq hepsilon
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _ hmax
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro increment hincrement
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hj1 := j1EDist_normalizedStepPath_linear_le
    (fun n => Real.sqrt n) n increment
  change ENNReal.ofReal epsilon ≤ edist
    (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
    (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment) at hincrement
  rw [Skorokhod.edist_cadlagPath_eq_j1EDist] at hincrement
  simp only [abs_inv, abs_of_pos hsqrt] at hj1
  have hbound := hincrement.trans hj1
  have hmaxNonneg : 0 ≤ (Real.sqrt n)⁻¹ * maxAbsUpTo n increment :=
    mul_nonneg (inv_nonneg.2 hsqrt.le) (maxAbsUpTo_nonneg n increment)
  rw [ENNReal.ofReal_le_ofReal_iff hmaxNonneg] at hbound
  rw [le_inv_mul_iff₀ hsqrt] at hbound
  change epsilon * Real.sqrt n ≤ maxAbsUpTo n increment
  simpa only [mul_comm] using hbound

/-- Real-distance form of the preceding Skorokhod interpolation estimate. -/
theorem tendsto_measureReal_dist_normalizedStepPath_linear_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (iidSequenceLaw nu).real
        {increment | epsilon ≤
          dist
            (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
            (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment)})
      atTop (nhds 0) := by
  have h := tendsto_measureReal_edist_normalizedStepPath_linear_zero
    nu hsq hepsilon
  apply h.congr'
  filter_upwards [] with n
  congr 1
  ext increment
  simp only [Set.mem_ofPred_eq, edist_dist]
  rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]

end ProbabilityTheory.RandomWalk
