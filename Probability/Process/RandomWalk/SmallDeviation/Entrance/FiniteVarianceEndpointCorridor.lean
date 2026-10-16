/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.FiniteVariance.StableEndpointBridge
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Path.Law
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
public import Probability.Distributions.Gaussian.Interval

/-!
# A finite variance corridor lower bound

The public definitions and theorem are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength` and `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength`:
  $\lfloor\Delta_n^2\rfloor$ and the remaining horizon
  $n-\lfloor\Delta_n^2\rfloor$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_iidSequenceLaw_endpointCorridor_lowerBound_of_centeredSecondMoment`:
  for a centered increment law with positive finite variance, the
  entrance probability times the stable endpoint-bridge probability
  bounds below the chance of remaining in the enlarged corridor and
  ending in its terminal unit-width window.

The diffusive entrance estimate and the stable endpoint-core bridge combine
to give a quantitative lower bound for a full random-walk corridor event.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The diffusive entrance block used at corridor width `scale n`. -/
noncomputable def finiteVarianceEntranceLength (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊scale n ^ 2⌋₊

/-- The remainder of a horizon after its diffusive entrance block. -/
noncomputable def finiteVarianceBridgeLength (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  n - finiteVarianceEntranceLength scale n

/-- Under only a centered finite second moment, a random walk has a
quantitative probability of staying in a wider corridor and ending in its
terminal window. The bound is the finite-variance entrance probability times
the stable endpoint-core bridge probability. -/
theorem exists_eventually_iidSequenceLaw_endpointCorridor_lowerBound_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (ratio : ℝ) (hratio : 1 < ratio) :
    ∃ C : ℝ, C < 0 ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ENNReal.ofReal (Real.exp
          ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
            (Asymptotics.balancedBlockCount
              (finiteVarianceBridgeLength scale n -
                stableBlockLength 2 ν (amplitude ^ (2 : ℝ))
                  scale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ))
                scale n) + 1) *
            (q / (finiteVarianceEntranceLength scale n : ℝ≥0∞)) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              InClosedInterval (-ratio * scale n) 0 n 0 increment ∧
              AdditivePath.displacement n increment ∈
                Set.Icc (-ratio * scale n) ((-ratio + 1) * scale n)} := by
  have hsecond : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hν.2]
    exact sq_pos_of_pos hsigma
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (ne_of_gt hsecond)
  let normalization : ℕ → ℝ := fun n => sigma * Real.sqrt n
  have hDOAraw :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hν.1 hsquare hsecond
  have hnormalizationEq :
      (fun n : ℕ => Real.sqrt ((n : ℝ) * ∫ x : ℝ, x ^ 2 ∂ν)) =
        normalization := by
    funext n
    rw [hν.2]
    dsimp [normalization]
    calc
      Real.sqrt ((n : ℝ) * sigma ^ 2) =
          Real.sqrt (sigma ^ 2 * (n : ℝ)) := by rw [mul_comm]
      _ = Real.sqrt (sigma ^ 2) * Real.sqrt (n : ℝ) :=
        Real.sqrt_mul (sq_nonneg sigma) (n : ℝ)
      _ = sigma * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0) := by
    simpa only [hnormalizationEq] using hDOAraw
  have hnormalizationPos : ∀ n : ℕ, 0 < n → 0 < normalization n := by
    intro n hn
    dsimp [normalization]
    exact mul_pos hsigma (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hstableNorming : IsStableNorming 2 ν normalization :=
    hDOA.isStableNorming_two_of_gaussian hnormalizationPos
  have hscaleSmall : Asymptotics.IsSmallDeviationScale scale normalization := by
    have hratioNorm : Tendsto
        (fun n : ℕ => normalization n / Real.sqrt n) atTop (nhds sigma) := by
      have heq : (fun n : ℕ => normalization n / Real.sqrt n) =ᶠ[atTop]
          fun _ => sigma := by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
        have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
        dsimp [normalization]
        rw [mul_div_assoc, div_self hroot.ne', mul_one]
      exact tendsto_const_nhds.congr' heq.symm
    have hrootPos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact Real.sqrt_pos.2 (by exact_mod_cast hn)
    exact hscale.of_tendsto_normalization_ratio hrootPos hratioNorm hsigma
  have hstableScale : IsStableMogulskiiScale 2 ν normalization scale :=
    ⟨hstableNorming, hscaleSmall⟩
  have hslow := hDOA.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have htight :=
    RandomWalk.FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hnormalizationPos
  have hstableGaussian : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  obtain ⟨P, hP, C, hEscape⟩ :=
    exists_generatedStableProcess_escapeRate_of_tightSource
      hDOA hstableGaussian htight hcdf
  let hX := iidUnitPathBlockProcess_isStableLevyProcess hP
  letI : IsProbabilityMeasure
      (iidUnitPathBlockLaw (P : Measure (CadlagPath unitInterval ℝ))) :=
    iidUnitPathBlockLaw_isProbabilityMeasure _
  have hEscape' : HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      ((hX.unitIntervalPathLaw) : Measure (CadlagPath unitInterval ℝ)) C := by
    simpa [hX] using hEscape
  have hC : C < 0 := hEscape'.negative
  obtain ⟨q, hqpos, Delta₀, hentry⟩ :=
    exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
      hν hsigma 0 (by norm_num)
  let bridgeLength := finiteVarianceBridgeLength scale
  have hscaleSqZero : Tendsto (fun n : ℕ => scale n ^ 2 / (n : ℝ))
      atTop (nhds 0) := hscale.tendsto_sq_div_natCast_zero
  have hprefixRatio : Tendsto
      (fun n : ℕ => (finiteVarianceEntranceLength scale n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hfloor : (finiteVarianceEntranceLength scale n : ℝ) ≤ scale n ^ 2 := by
        dsimp [finiteVarianceEntranceLength]
        exact Nat.floor_le (by positivity)
      exact div_le_div_of_nonneg_right hfloor hnReal.le
    · exact hscaleSqZero
  have hprefixLe : ∀ᶠ n : ℕ in atTop,
      finiteVarianceEntranceLength scale n ≤ n := by
    have hsmallRatio : ∀ᶠ n : ℕ in atTop,
        (finiteVarianceEntranceLength scale n : ℝ) / (n : ℝ) < 1 :=
      hprefixRatio.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hsmallRatio, eventually_gt_atTop (0 : ℕ)] with n hr hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlt : (finiteVarianceEntranceLength scale n : ℝ) < (n : ℝ) := by
      have hlt' := (div_lt_iff₀ hnReal).mp hr
      simpa only [one_mul] using hlt'
    exact le_of_lt (by exact_mod_cast hlt)
  have hbridgeRatio : Tendsto (fun n : ℕ => (bridgeLength n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have hdiff : Tendsto
        (fun n : ℕ => 1 - (finiteVarianceEntranceLength scale n : ℝ) / (n : ℝ))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hprefixRatio
    have heq : (fun n : ℕ => (bridgeLength n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => 1 - (finiteVarianceEntranceLength scale n : ℝ) / (n : ℝ) := by
      filter_upwards [hprefixLe, eventually_gt_atTop (0 : ℕ)] with n hle hn
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      dsimp [bridgeLength, finiteVarianceBridgeLength]
      rw [Nat.cast_sub hle]
      field_simp [hnReal]
    exact hdiff.congr' heq.symm
  obtain ⟨amplitude, hamplitude, hbridge⟩ :=
    exists_eventually_iidSequenceLaw_rightEndpointBridge_ge_stableCellLowerBound
      hstableScale hslow hEscape' hX hcdf hDOA htight ratio hratio
      bridgeLength (by norm_num) hbridgeRatio
  have hentryEventual : ∀ᶠ n : ℕ in atTop, Delta₀ ≤ scale n :=
    hscale.tendsto_atTop.eventually_ge_atTop Delta₀
  have hscalePositive : ∀ᶠ n : ℕ in atTop, 0 < scale n := hscale.eventually_pos
  refine ⟨C, hC, q, hqpos, amplitude, hamplitude, ?_⟩
  have hfinalEventually : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
          (Asymptotics.balancedBlockCount
            (bridgeLength n - stableBlockLength 2 ν (amplitude ^ (2 : ℝ))
              scale n)
            (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1) *
          (q / (finiteVarianceEntranceLength scale n : ℝ≥0∞)) ≤
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            InClosedInterval (-ratio * scale n) 0 n 0 increment ∧
            AdditivePath.displacement n increment ∈
              Set.Icc (-ratio * scale n) ((-ratio + 1) * scale n)} := by
    filter_upwards [hbridge, hentryEventual, hscalePositive, hprefixLe] with
      n hbridgeN hentryN hscaleN hprefixN
    have hentryN' : q / (finiteVarianceEntranceLength scale n : ℝ≥0∞) ≤
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            (Combinatorics.Sequence.blockCoordinates 0
              (finiteVarianceEntranceLength scale n)) increment ∈
              finiteMovingEntranceEvent (n := finiteVarianceEntranceLength scale n)
                (scale n) 0 1} := by
      have h := hentry (scale n) hentryN (-scale n) ⟨le_rfl, by linarith⟩
      have hratio : -(-scale n) / scale n = (1 : ℝ) := by
        rw [neg_neg, div_self hscaleN.ne']
      change q / (⌊(scale n) ^ 2⌋₊ : ℝ≥0∞) ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          (Combinatorics.Sequence.blockCoordinates 0
            ⌊(scale n) ^ 2⌋₊) increment ∈
            finiteMovingEntranceEvent (n := ⌊(scale n) ^ 2⌋₊) (scale n) 0 1}
      simpa only [hratio, zero_div] using h
    let entryLower : ℝ≥0∞ := q / (finiteVarianceEntranceLength scale n : ℝ≥0∞)
    let bridgeLower : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
        (Asymptotics.balancedBlockCount
          (bridgeLength n - stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n)
          (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1)
    have hbridgeN' : bridgeLower ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (bridgeLength n) increment ∈
            {block |
              RandomWalk.SmallDeviation.Mogulskii.Discrete.partitionCellCoreReturnBlockEvent
                (-ratio * scale n) 0 (-scale n / 2) (scale n / 6)
                ((-ratio + 1 / 2) * scale n) (scale n / 2) block}} := by
      have h1 : scale n * (-ratio) = -ratio * scale n := by ring
      have h2 : scale n * (0 : ℝ) = 0 := by ring
      have h3 : scale n * (-1 / 2) = -scale n / 2 := by ring
      have h4 : scale n * (1 / 6) = scale n / 6 := by ring
      have h5 : scale n * (-ratio + 1 / 2) = (-ratio + 1 / 2) * scale n := by ring
      have h6 : scale n * (1 / 2) = scale n / 2 := by ring
      simpa only [bridgeLower, h1, h2, h3, h4, h5, h6, Set.mem_setOf_eq] using hbridgeN
    have hcombined :=
      iidSequenceLaw_measure_mul_of_finiteMovingEntranceEvent_bridge
        ν (finiteVarianceEntranceLength scale n) (bridgeLength n) (scale n) ratio
        hscaleN hratio entryLower bridgeLower hentryN' hbridgeN'
    have hlength : finiteVarianceEntranceLength scale n + bridgeLength n = n := by
      simp [bridgeLength, finiteVarianceBridgeLength]
      omega
    simpa [entryLower, bridgeLower, hlength] using hcombined
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hfinalEventually
  exact ⟨n₀, hn₀⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
