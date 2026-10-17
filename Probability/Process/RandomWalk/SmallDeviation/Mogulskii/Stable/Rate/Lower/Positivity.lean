/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Lower.BlockProbability
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Positivity and logarithmic bounds for stable tube probabilities

Let $s_n=\mathrm{scale}(n)$,
$L^*(x)=\mathrm{stableSlowVariation}(\alpha,\nu)(x)$,
$a_n=s_n^\alpha/(nL^*(s_n))$, and
$T_n=\{|S_j|<s_n/2\text{ for }1\leq j\leq n\}$ for partial sums of
i.i.d. increments with law $\nu$. Assume $0<\alpha\leq2$, a stable
Mogulskii scale, $a_n\to0$, slow variation of $L^*$, the stable-process
escape-rate hypothesis, and the domain-of-attraction, tightness, and
endpoint-sign conditions. The public declaration is:

- `stableEscapeRate_eventually_positive_and_log_cobounded`: eventually
  $\mathbb P(T_n)>0$; moreover $a_n\log\mathbb P(T_n)$ is eventually bounded
  above and below and is cobounded under $\leq$.

This is an auxiliary consequence of the endpoint-return lower estimate in
Theorem 3, Section 4 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. It provides the real-logarithm conditions used by the stable
upper-rate and limit arguments.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- The endpoint-return estimate from Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081, supplies eventual
positivity and the real-logarithm bounds required by the upper Portmanteau
argument. The slowly varying factor need not be bounded along the scale. -/
theorem stableEscapeRate_eventually_positive_and_log_cobounded
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    (∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) ∧
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun n => stableSmallDeviationRate α ν scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw ν)
            (1 / 2) (scale n) n).toReal) := by
  have hfixed :=
    eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (0 : ℝ) < 1 / 64)
      (by norm_num : 4 * (1 / 64 : ℝ) < 1 / 3)
      (by norm_num : 2 * (1 / 3 + 4 * (1 / 64 : ℝ)) < 1)
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨c, hc, hprobLower⟩ := hfixed
  let radius : ℝ := 1 / 3
  let epsilon : ℝ := 1 / 64
  let delta : ℝ := 1
  let constant : ℝ := c ^ α
  let length : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let count : ℕ → ℕ := fun n => stableBlockCount α ν constant scale n
  let probability : ℕ → ℝ≥0∞ := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n
  let base : ℝ := Real.exp ((C / radius ^ α - delta) * constant)
  let baseENN : ℝ≥0∞ := ENNReal.ofReal base
  let coefficient : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n * ((count n + 1 : ℕ) : ℝ)
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact Real.rpow_pos_of_pos hc α
  have hbasePos : 0 < base := by
    dsimp [base]
    exact Real.exp_pos _
  have hbaseENNPos : 0 < baseENN := ENNReal.ofReal_pos.mpr hbasePos
  have hbaseENNPowPos : ∀ k : ℕ, 0 < baseENN ^ k := by
    intro k
    exact pos_iff_ne_zero.mpr (ENNReal.pow_ne_zero hbaseENNPos.ne' k)
  have hprobLower' : ∀ᶠ n in atTop,
      baseENN ^ (n / length n + 1) ≤ probability n := by
    filter_upwards [hprobLower] with n hn
    simpa [baseENN, base, radius, delta, length, count, probability,
      stableBlockCount] using hn
  have hpositive : ∀ᶠ n in atTop, 0 < probability n := by
    filter_upwards [hprobLower'] with n hn
    exact (hbaseENNPowPos _).trans_le hn
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hcountRate :=
    tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
      hα hα₂ hconstant hscale hslow hrate
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hscalePos := IsStableMogulskiiScale.eventually_scale_pos hscale
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hslowPos]
      with n hn hs hL
    rw [stableSmallDeviationRate, stableScaleTime]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal, hL.ne']
  have hcountTerm : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n * (count n : ℝ))
      atTop (𝓝 constant⁻¹) := by
    apply hcountRate.congr'
    filter_upwards [hrateEq] with n hn
    simp [count, stableBlockCount, hn]
  have hcoefficient : Tendsto coefficient atTop (𝓝 constant⁻¹) := by
    have hsum := hcountTerm.add hrate
    have heq : coefficient =ᶠ[atTop]
        fun n => stableSmallDeviationRate α ν scale n * (count n : ℝ) +
          stableSmallDeviationRate α ν scale n := by
      filter_upwards [] with n
      simp [coefficient]
      ring
    simpa [coefficient] using hsum.congr' heq.symm
  have hleft : Tendsto (fun n => coefficient n * Real.log base)
      atTop (𝓝 (constant⁻¹ * Real.log base)) := hcoefficient.mul_const _
  have hlog : ∀ᶠ n in atTop,
      coefficient n * Real.log base ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hprobLower', hpositive,
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      eventually_gt_atTop (0 : ℕ),
      hscaleTop.eventually hslow.eventually_pos]
      with n hbound hpos hs hn hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : baseENN ^ (n / length n + 1) ≠ ∞ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hreal : base ^ (n / length n + 1) ≤ (probability n).toReal := by
      have h := (ENNReal.toReal_le_toReal hpowTop hprobTop).2 hbound
      simpa [baseENN, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hbasePos.le] using h
    have hlogReal : ((n / length n + 1 : ℕ) : ℝ) * Real.log base ≤
        Real.log (probability n).toReal := by
      have h := Real.log_le_log (pow_pos hbasePos _) hreal
      simpa [Real.log_pow] using h
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    calc
      coefficient n * Real.log base =
          stableSmallDeviationRate α ν scale n *
            ((n / length n + 1 : ℕ) : ℝ) * Real.log base := by
        have hcountEq : count n = n / length n := by
          simp [count, stableBlockCount, length]
        simp [coefficient, hcountEq]
      _ ≤ stableSmallDeviationRate α ν scale n *
            Real.log (probability n).toReal := by
        nlinarith [mul_le_mul_of_nonneg_left hlogReal hrateNonneg]
  have hleftLower : ∀ᶠ n in atTop,
      constant⁻¹ * Real.log base - 1 < coefficient n * Real.log base :=
    hleft.eventually (Ioi_mem_nhds (by linarith :
      constant⁻¹ * Real.log base - 1 < constant⁻¹ * Real.log base))
  have hactualLower : ∀ᶠ n in atTop,
      constant⁻¹ * Real.log base - 1 ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hleftLower, hlog] with n hleftN hlogN
    exact hleftN.le.trans hlogN
  have hactualUpper : ∀ᶠ n in atTop,
      stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [IsStableMogulskiiScale.eventually_scale_pos hscale,
      eventually_gt_atTop (0 : ℕ),
      hscaleTop.eventually hslow.eventually_pos] with n hs hn hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hprobRealOne : (probability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hrateNonneg
      (Real.log_nonpos ENNReal.toReal_nonneg hprobRealOne)
  refine ⟨hpositive,
    Filter.isCoboundedUnder_le_of_eventually_le atTop hactualLower,
    ⟨constant⁻¹ * Real.log base - 1, hactualLower⟩,
    ⟨0, hactualUpper⟩⟩


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

end
