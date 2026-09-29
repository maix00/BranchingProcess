import Combinatorics.BranchingWalk.Walk.Path.Truncation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space
import Probability.Independence.Moment.Fourth
import Probability.BranchingRandomWalk.Walk.Path.Moment.Fourth

/-!
# Moments of truncated increments

Hard truncation turns a finite second moment into a finite fourth moment.  The
centering operation is kept in the probability layer because it depends on
the increment law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A hard-truncated increment is integrable whenever the original increment
is integrable. -/
theorem integrable_truncatedIncrement {ν : Measure ℝ}
    (h : Integrable (fun x : ℝ => x) ν) (radius : ℝ) :
    Integrable (truncatedIncrement radius) ν :=
  h.mono (measurable_truncatedIncrement radius).aestronglyMeasurable
    (ae_of_all ν fun x => by
      simpa only [Real.norm_eq_abs] using
        abs_truncatedIncrement_le_abs radius x)

/-- A finite second moment gives integrability of the fourth power after hard
truncation. -/
theorem integrable_truncatedIncrement_pow_four {ν : Measure ℝ}
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    Integrable (fun x => truncatedIncrement radius x ^ 4) ν := by
  have hbound : Integrable (fun x : ℝ => radius ^ 2 * x ^ 2) ν :=
    hsq.const_mul (radius ^ 2)
  exact hbound.mono
    ((measurable_truncatedIncrement radius).pow_const 4).aestronglyMeasurable
    (ae_of_all ν fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ truncatedIncrement radius x ^ 4),
        abs_of_nonneg (mul_nonneg (sq_nonneg radius) (sq_nonneg x))]
      exact truncatedIncrement_pow_four_le hradius)

/-- Integrated fourth-moment estimate for hard truncation. -/
theorem integral_truncatedIncrement_pow_four_le {ν : Measure ℝ}
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    (∫ x, truncatedIncrement radius x ^ 4 ∂ν) ≤
      radius ^ 2 * ∫ x, x ^ 2 ∂ν := by
  rw [← integral_const_mul]
  exact integral_mono
    (integrable_truncatedIncrement_pow_four hsq hradius)
    (hsq.const_mul (radius ^ 2))
    (fun x => truncatedIncrement_pow_four_le hradius)

/-- Mean of the hard-truncated one-step increment. -/
noncomputable def truncatedIncrementMean (ν : Measure ℝ) (radius : ℝ) : ℝ :=
  ∫ x, truncatedIncrement radius x ∂ν

/-- Centered hard truncation of an increment. -/
noncomputable def centeredTruncatedIncrement
    (ν : Measure ℝ) (radius x : ℝ) : ℝ :=
  truncatedIncrement radius x - truncatedIncrementMean ν radius

theorem measurable_centeredTruncatedIncrement (ν : Measure ℝ) (radius : ℝ) :
    Measurable (centeredTruncatedIncrement ν radius) :=
  (measurable_truncatedIncrement radius).sub measurable_const

theorem integrable_centeredTruncatedIncrement
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : Integrable (fun x : ℝ => x) ν) (radius : ℝ) :
    Integrable (centeredTruncatedIncrement ν radius) ν := by
  exact (integrable_truncatedIncrement h radius).sub (integrable_const _)

/-- Under a probability law, a finite second moment is enough to center the
hard truncation. -/
theorem integrable_centeredTruncatedIncrement_of_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν) (radius : ℝ) :
    Integrable (centeredTruncatedIncrement ν radius) ν := by
  have hmem : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  exact integrable_centeredTruncatedIncrement ν
    (hmem.integrable (by norm_num)) radius

/-- Centering really gives mean zero for a probability increment law. -/
theorem integral_centeredTruncatedIncrement
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : Integrable (fun x : ℝ => x) ν) (radius : ℝ) :
    ∫ x, centeredTruncatedIncrement ν radius x ∂ν = 0 := by
  change (∫ x, truncatedIncrement radius x -
    truncatedIncrementMean ν radius ∂ν) = 0
  rw [integral_sub (integrable_truncatedIncrement h radius)
      (integrable_const _), integral_const]
  simp [Measure.real, truncatedIncrementMean]

theorem integral_centeredTruncatedIncrement_of_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν) (radius : ℝ) :
    ∫ x, centeredTruncatedIncrement ν radius x ∂ν = 0 := by
  have hmem : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  exact integral_centeredTruncatedIncrement ν
    (hmem.integrable (by norm_num)) radius

/-- The truncated mean stays in the same symmetric truncation interval. -/
theorem abs_truncatedIncrementMean_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius) :
    |truncatedIncrementMean ν radius| ≤ radius := by
  change ‖∫ x, truncatedIncrement radius x ∂ν‖ ≤ radius
  have h := norm_integral_le_of_norm_le_const
    (μ := ν) (f := truncatedIncrement radius) (C := radius)
    (ae_of_all ν fun x => by
      simpa only [Real.norm_eq_abs] using
        abs_truncatedIncrement_le (x := x) hradius)
  simpa [Measure.real] using h

/-- For a centered increment law, the mean introduced by hard truncation is
exactly the negative mean of the discarded tail. -/
theorem truncatedIncrementMean_eq_neg_integral_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (radius : ℝ) :
    truncatedIncrementMean ν radius =
      -(∫ x, {y : ℝ | radius < |y|}.indicator (fun y => y) x ∂ν) := by
  let tail : Set ℝ := {y | radius < |y|}
  have htail : MeasurableSet tail :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have htailInt : Integrable (tail.indicator fun y : ℝ => y) ν :=
    hint.indicator htail
  have htrunc := integrable_truncatedIncrement hint radius
  have hpointwise : ∀ x : ℝ,
      truncatedIncrement radius x + tail.indicator (fun y : ℝ => y) x = x := by
    intro x
    by_cases hx : |x| ≤ radius
    · rw [truncatedIncrement_of_abs_le hx,
        Set.indicator_of_notMem (show x ∉ tail from not_lt_of_ge hx)]
      simp
    · have hx' : radius < |x| := lt_of_not_ge hx
      rw [truncatedIncrement_of_lt_abs hx',
        Set.indicator_of_mem (show x ∈ tail from hx')]
      simp
  have hsum : truncatedIncrementMean ν radius +
      (∫ x, tail.indicator (fun y : ℝ => y) x ∂ν) = 0 := by
    unfold truncatedIncrementMean
    rw [← integral_add htrunc htailInt]
    simpa only [hpointwise] using hcentered
  change truncatedIncrementMean ν radius =
    -(∫ x, tail.indicator (fun y : ℝ => y) x ∂ν)
  linarith

/-- The absolute truncated mean is controlled by the first absolute moment
of the discarded tail. -/
theorem abs_truncatedIncrementMean_le_integral_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (radius : ℝ) :
    |truncatedIncrementMean ν radius| ≤
      ∫ x, {y : ℝ | radius < |y|}.indicator (fun y => |y|) x ∂ν := by
  rw [truncatedIncrementMean_eq_neg_integral_tail ν hint hcentered radius,
    abs_neg]
  let tail : Set ℝ := {y | radius < |y|}
  have hfun : (fun x => ‖tail.indicator (fun y : ℝ => y) x‖) =
      tail.indicator (fun y => |y|) := by
    funext x
    by_cases hx : x ∈ tail <;> simp [hx, Real.norm_eq_abs]
  change |∫ x, tail.indicator (fun y : ℝ => y) x ∂ν| ≤
    ∫ x, tail.indicator (fun y => |y|) x ∂ν
  rw [← hfun]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm
      (tail.indicator fun y : ℝ => y) (μ := ν))

/-- Multiplying the truncation bias by the cutoff converts its first-moment
tail bound into the discarded second moment. -/
theorem radius_mul_abs_truncatedIncrementMean_le_integral_tail_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    radius * |truncatedIncrementMean ν radius| ≤
      ∫ x, {y : ℝ | radius < |y|}.indicator (fun y => y ^ 2) x ∂ν := by
  let tail : Set ℝ := {y | radius < |y|}
  have htail : MeasurableSet tail :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hmem : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  have hint : Integrable (fun x : ℝ => x) ν :=
    hmem.integrable (by norm_num)
  have hbias := abs_truncatedIncrementMean_le_integral_tail
    ν hint hcentered radius
  calc
    radius * |truncatedIncrementMean ν radius| ≤
        radius * ∫ x, tail.indicator (fun y => |y|) x ∂ν :=
      mul_le_mul_of_nonneg_left hbias hradius
    _ = ∫ x, tail.indicator (fun y => radius * |y|) x ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext x
      by_cases hx : x ∈ tail <;> simp [hx]
    _ ≤ ∫ x, tail.indicator (fun y => y ^ 2) x ∂ν := by
      refine integral_mono
        ((hint.norm.const_mul radius).indicator htail)
        (hsq.indicator htail) ?_
      intro x
      by_cases hx : x ∈ tail
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have hx' : radius ≤ |x| := (show radius < |x| from hx).le
        have hmul := mul_le_mul_of_nonneg_right hx' (abs_nonneg x)
        simpa only [abs_mul_abs_self, pow_two] using hmul
      · simp [Set.indicator_of_notMem hx]

/-- Pointwise fourth-power bound for the centered truncation.  The numerical
constant is inessential; its role is to expose a fourth moment controlled by
the original second moment and the cutoff. -/
theorem centeredTruncatedIncrement_pow_four_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius x : ℝ} (hradius : 0 ≤ radius) :
    centeredTruncatedIncrement ν radius x ^ 4 ≤
      8 * (radius ^ 2 * x ^ 2 + radius ^ 4) := by
  let a := truncatedIncrement radius x
  let b := truncatedIncrementMean ν radius
  have hab : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b),
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2)]
  have ha : a ^ 4 ≤ radius ^ 2 * x ^ 2 :=
    truncatedIncrement_pow_four_le hradius
  have hbabs : |b| ≤ radius := abs_truncatedIncrementMean_le ν hradius
  have hb : b ^ 4 ≤ radius ^ 4 := by
    have hs : b ^ 2 ≤ radius ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hradius]
      exact hbabs
    calc
      b ^ 4 = b ^ 2 * b ^ 2 := by ring
      _ ≤ radius ^ 2 * radius ^ 2 :=
        mul_le_mul hs hs (sq_nonneg b) (sq_nonneg radius)
      _ = radius ^ 4 := by ring
  change (a - b) ^ 4 ≤ _
  exact hab.trans (mul_le_mul_of_nonneg_left (add_le_add ha hb) (by norm_num))

/-- Pointwise fourth-power bound which retains the actual truncated mean.
Unlike `centeredTruncatedIncrement_pow_four_le`, this estimate does not replace
that mean by the truncation radius and is therefore suitable when the radius
depends on the number of summands. -/
theorem centeredTruncatedIncrement_pow_four_le_mean
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius x : ℝ} (hradius : 0 ≤ radius) :
    centeredTruncatedIncrement ν radius x ^ 4 ≤
      8 * (radius ^ 2 * x ^ 2 + truncatedIncrementMean ν radius ^ 4) := by
  let a := truncatedIncrement radius x
  let b := truncatedIncrementMean ν radius
  have hab : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b),
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2)]
  have ha : a ^ 4 ≤ radius ^ 2 * x ^ 2 :=
    truncatedIncrement_pow_four_le hradius
  change (a - b) ^ 4 ≤ _
  exact hab.trans
    (mul_le_mul_of_nonneg_left (add_le_add ha le_rfl) (by norm_num))

/-- The centered hard truncation has a finite fourth moment under only a
finite second moment of the original increment law. -/
theorem integrable_centeredTruncatedIncrement_pow_four
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    Integrable (fun x => centeredTruncatedIncrement ν radius x ^ 4) ν := by
  have hmajorant : Integrable
      (fun x : ℝ => 8 * (radius ^ 2 * x ^ 2 + radius ^ 4)) ν :=
    ((hsq.const_mul (radius ^ 2)).add (integrable_const _)).const_mul 8
  exact hmajorant.mono
    ((measurable_centeredTruncatedIncrement ν radius).pow_const 4).aestronglyMeasurable
    (ae_of_all ν fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity :
          0 ≤ centeredTruncatedIncrement ν radius x ^ 4),
        abs_of_nonneg (by positivity :
          0 ≤ 8 * (radius ^ 2 * x ^ 2 + radius ^ 4))]
      exact centeredTruncatedIncrement_pow_four_le ν hradius)

theorem memLp_centeredTruncatedIncrement_four
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    MemLp (centeredTruncatedIncrement ν radius) 4 ν := by
  rw [memLp_four_iff_integrable_pow_four
    (measurable_centeredTruncatedIncrement ν radius).aestronglyMeasurable]
  exact integrable_centeredTruncatedIncrement_pow_four ν hsq hradius

/-- Centering a hard truncation cannot increase its second moment beyond the
original second moment. -/
theorem integral_centeredTruncatedIncrement_sq_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (radius : ℝ) :
    (∫ x, centeredTruncatedIncrement ν radius x ^ 2 ∂ν) ≤
      ∫ x, x ^ 2 ∂ν := by
  have hId : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  have htrunc : MemLp (truncatedIncrement radius) 2 ν :=
    hId.mono (measurable_truncatedIncrement radius).aestronglyMeasurable
      (ae_of_all ν fun x => by
        simpa only [Real.norm_eq_abs] using
          abs_truncatedIncrement_le_abs radius x)
  have hvariance : variance (truncatedIncrement radius) ν =
      ∫ x, centeredTruncatedIncrement ν radius x ^ 2 ∂ν := by
    rw [variance_eq_integral
      (measurable_truncatedIncrement radius).aemeasurable]
    rfl
  rw [← hvariance, variance_eq_sub htrunc]
  calc
    (∫ x, truncatedIncrement radius x ^ 2 ∂ν) -
        (∫ x, truncatedIncrement radius x ∂ν) ^ 2 ≤
        ∫ x, truncatedIncrement radius x ^ 2 ∂ν :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ ∫ x, x ^ 2 ∂ν := by
      have htruncSq : Integrable
          (fun x => truncatedIncrement radius x ^ 2) ν :=
        (memLp_two_iff_integrable_sq
          (measurable_truncatedIncrement radius).aestronglyMeasurable).1 htrunc
      exact integral_mono htruncSq hsq fun x => by
        have h := abs_truncatedIncrement_le_abs radius x
        rw [← sq_abs (truncatedIncrement radius x), ← sq_abs x]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Quantitative fourth-moment estimate for the centered truncation. -/
theorem integral_centeredTruncatedIncrement_pow_four_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    (∫ x, centeredTruncatedIncrement ν radius x ^ 4 ∂ν) ≤
      8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν + radius ^ 4) := by
  have hmajorant : Integrable
      (fun x : ℝ => 8 * (radius ^ 2 * x ^ 2 + radius ^ 4)) ν :=
    ((hsq.const_mul (radius ^ 2)).add (integrable_const _)).const_mul 8
  calc
    (∫ x, centeredTruncatedIncrement ν radius x ^ 4 ∂ν) ≤
        ∫ x, 8 * (radius ^ 2 * x ^ 2 + radius ^ 4) ∂ν :=
      integral_mono
        (integrable_centeredTruncatedIncrement_pow_four ν hsq hradius)
        hmajorant
        (fun x => centeredTruncatedIncrement_pow_four_le ν hradius)
    _ = 8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν + radius ^ 4) := by
      rw [integral_const_mul, integral_add, integral_const_mul, integral_const]
      · simp [Measure.real]
      · exact hsq.const_mul (radius ^ 2)
      · exact integrable_const _

/-- Integrated centered fourth-moment estimate retaining the actual truncated
mean.  This is the quantitative form used for growing truncation radii. -/
theorem integral_centeredTruncatedIncrement_pow_four_le_mean
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    (∫ x, centeredTruncatedIncrement ν radius x ^ 4 ∂ν) ≤
      8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
        truncatedIncrementMean ν radius ^ 4) := by
  have hmajorant : Integrable
      (fun x : ℝ => 8 * (radius ^ 2 * x ^ 2 +
        truncatedIncrementMean ν radius ^ 4)) ν :=
    ((hsq.const_mul (radius ^ 2)).add (integrable_const _)).const_mul 8
  calc
    (∫ x, centeredTruncatedIncrement ν radius x ^ 4 ∂ν) ≤
        ∫ x, 8 * (radius ^ 2 * x ^ 2 +
          truncatedIncrementMean ν radius ^ 4) ∂ν :=
      integral_mono
        (integrable_centeredTruncatedIncrement_pow_four ν hsq hradius)
        hmajorant
        (fun x => centeredTruncatedIncrement_pow_four_le_mean ν hradius)
    _ = 8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
        truncatedIncrementMean ν radius ^ 4) := by
      rw [integral_const_mul, integral_add, integral_const_mul, integral_const]
      · simp [Measure.real]
      · exact hsq.const_mul (radius ^ 2)
      · exact integrable_const _

/-- Fourth moment of a partial sum whose IID increments are the centered hard
truncations of a finite-second-moment law.  The bound is stated entirely in
terms of the original law, the cutoff, and the actual truncation bias. -/
theorem integral_partialSum_pow_four_centeredTruncated_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius) (n : ℕ) :
    (∫ path : ℕ → ℝ, partialSum n path ^ 4 ∂
        iidSequenceLaw (ν.map (centeredTruncatedIncrement ν radius))) ≤
      (n : ℝ) *
          (8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
            truncatedIncrementMean ν radius ^ 4)) +
        3 * (n : ℝ) ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2 := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmem4Source : MemLp f 4 ν :=
    memLp_centeredTruncatedIncrement_four ν hsq hradius
  have hmem4Map : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmem4Source
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement_of_integrable_sq
        ν hsq radius
  have hbase := integral_partialSum_pow_four_iidSequenceLaw_le
    (ν.map f) hmem4Map hcenteredMap n
  have hfour : (∫ x, x ^ 4 ∂ν.map f) = ∫ x, f x ^ 4 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 4).aestronglyMeasurable
  have htwo : (∫ x, x ^ 2 ∂ν.map f) = ∫ x, f x ^ 2 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable
  rw [hfour, htwo] at hbase
  refine hbase.trans ?_
  have hfourLe :=
    integral_centeredTruncatedIncrement_pow_four_le_mean ν hsq hradius
  have htwoLe := integral_centeredTruncatedIncrement_sq_le ν hsq radius
  have hn : 0 ≤ (n : ℝ) := by positivity
  have htwoNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have horiginalNonneg : 0 ≤ ∫ x, x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have htwoSq : (∫ x, f x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, x ^ 2 ∂ν) ^ 2 := by
    exact pow_le_pow_left₀ htwoNonneg htwoLe 2
  nlinarith

end ProbabilityTheory.RandomWalk
