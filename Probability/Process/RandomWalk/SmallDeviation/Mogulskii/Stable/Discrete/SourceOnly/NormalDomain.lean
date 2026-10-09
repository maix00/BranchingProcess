/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.StableDomain
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRelative
public import Probability.Distributions.Stable.Gaussian
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.Distributions.Stable.Attraction.Normal

/-!
# Source-only normal-domain Mogul'skii rates

The variance of the strict two-stable limit and the raw norming time constant
are exposed separately. Rescaling by the reciprocal standard deviation turns
the limit into the standard Gaussian used by the normal-domain tightness and
escape-rate theorems.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

/-- Constants and finite-corridor rates produced from a raw normal-domain
source. The record names each normalization factor so callers can inspect or
reuse the source calculation without unpacking an anonymous conjunction. -/
structure RawNormalSourceRateData
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (scale : ℕ → ℝ) where
  variance : ℝ≥0
  spatialFactor : ℝ
  timeFactor : ℝ
  sourceEscapeConstant : ℝ
  variance_pos : 0 < (variance : ℝ)
  sourceLaw_eq_gaussian : μ = gaussianReal 0 variance
  scale_tendsto_atTop : Tendsto scale atTop atTop
  spatialFactor_pos : 0 < spatialFactor
  spatialVariance_eq_one : spatialFactor ^ 2 * (variance : ℝ) = 1
  timeFactor_eq_spatial_sq : timeFactor = spatialFactor ^ 2
  timeFactor_eq_inv_variance : timeFactor = (variance : ℝ)⁻¹
  timeFactor_pos : 0 < timeFactor
  sourceEscapeConstant_neg : sourceEscapeConstant < 0
  normalizedEscape_eq : timeFactor * sourceEscapeConstant = -(Real.pi ^ 2) / 8
  denominator_tendsto_atBot :
    Tendsto (probabilityRateDenominator 2 ν scale) atTop atBot
  finiteCorridorUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
    (∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}
      (iidSequenceLaw ν)) ∧
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) /
          probabilityRateDenominator 2 ν scale n)
      atTop (𝓝 (rateCoefficient 2 (timeFactor * sourceEscapeConstant) * C₃.realEnergy))

/-- Raw source inputs with a strictly two-stable limit yield all finite
corridor-union rates, packaged with named normalization fields. If the
limiting Gaussian has variance `v`, then the
spatial standardization is `q = 1 / √v` and the raw norming time constant is
`d = q² = 1 / v`. The escape rate after spatial standardization is
`-π² / 8`, so `d * Csource` is exactly that constant. -/
noncomputable def rawNormalSourceRateData_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0)) :
    RawNormalSourceRateData ν μ scale := by
  let hgaussian := hStable.exists_gaussianReal_zero
  let v : ℝ≥0 := Classical.choose hgaussian
  have hvne : v ≠ 0 := (Classical.choose_spec hgaussian).1
  have hμ : μ = gaussianReal 0 v := (Classical.choose_spec hgaussian).2
  have hvR : 0 < (v : ℝ) := by
    have hvRne : (v : ℝ) ≠ 0 := by exact_mod_cast hvne
    exact lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hvRne)
  let sigma : ℝ := Real.sqrt (v : ℝ)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hvR
  let q : ℝ := sigma⁻¹
  have hq : 0 < q := inv_pos.2 hsigma
  have hqvariance : q ^ 2 * (v : ℝ) = 1 := by
    calc
      q ^ 2 * (v : ℝ) = (sigma ^ 2)⁻¹ * (v : ℝ) := by simp [q]
      _ = (v : ℝ)⁻¹ * (v : ℝ) := by
        rw [Real.sq_sqrt (le_of_lt hvR)]
      _ = 1 := inv_mul_cancel₀ hvR.ne'
  have hq2 : q ^ 2 = (v : ℝ)⁻¹ := by
    field_simp [hvR.ne']
    exact hqvariance
  let d : ℝ := (v : ℝ)⁻¹
  have hd : 0 < d := inv_pos.2 hvR
  have hdq : d = q ^ 2 := by dsimp [d]; exact hq2.symm
  have hvarianceNN : v / ⟨sigma ^ 2, sq_nonneg sigma⟩ = 1 := by
    apply NNReal.eq
    change (v : ℝ) / sigma ^ 2 = 1
    rw [Real.sq_sqrt (le_of_lt hvR)]
    exact div_self (ne_of_gt hvR)
  have hgaussianMap :
      (gaussianReal 0 v).map (fun x : ℝ => x / sigma) = gaussianReal 0 1 := by
    have hmap := gaussianReal_map_div_const (μ := (0 : ℝ)) (v := v) sigma
    rw [hmap, zero_div]
    exact congrArg (gaussianReal 0) hvarianceNN
  have hmap : μ.map (fun x : ℝ => q * x) = gaussianReal 0 1 := by
    rw [hμ]
    have hfun : (fun x : ℝ => q * x) = fun x => x / sigma := by
      funext x
      simp [q, div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact hgaussianMap
  let standardNormalization : ℕ → ℝ := fun n => sigma * normalization n
  have hstandardNormalizationPos :
      ∀ᶠ n : ℕ in atTop, 0 < standardNormalization n := by
    filter_upwards [hDOA.eventually_scale_pos] with n hn
    exact mul_pos hsigma hn
  have hnormalizationRatio : Tendsto
      (fun n : ℕ => standardNormalization n / normalization n)
      atTop (𝓝 sigma) := by
    have heq : (fun n : ℕ => standardNormalization n / normalization n) =ᶠ[atTop]
        fun _ => sigma := by
      filter_upwards [hDOA.eventually_scale_pos] with n hn
      simp [standardNormalization, ne_of_gt hn]
    exact tendsto_const_nhds.congr' heq.symm
  have hsmallStandard : Asymptotics.IsSmallDeviationScale scale standardNormalization :=
    hsmall.of_tendsto_normalization_ratio hDOA.eventually_scale_pos
      hnormalizationRatio hsigma
  have hratioDOA : Tendsto
      (fun n : ℕ => normalization n / standardNormalization n)
      atTop (𝓝 q) := by
    have heq : (fun n : ℕ => normalization n / standardNormalization n) =ᶠ[atTop]
        fun _ => q := by
      filter_upwards [hDOA.eventually_scale_pos] with n hn
      simp [standardNormalization, q, div_eq_mul_inv, mul_comm, ne_of_gt hn]
    exact tendsto_const_nhds.congr' heq.symm
  have hDOAstandard0 : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      standardNormalization (fun _ => 0) := by
    simpa only [hmap] using
      hDOA.changeNormalization hstandardNormalizationPos hq hratioDOA
  let hinputs := exists_source_gaussian_mogulskii_inputs hsmallStandard hDOAstandard0
  let normalization' : ℕ → ℝ := Classical.choose hinputs
  have hinputsSpec := Classical.choose_spec hinputs
  have hscale : IsStableMogulskiiScale 2 ν normalization' scale := hinputsSpec.1
  have hDOAstandard : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization' (fun _ => 0) := hinputsSpec.2.2
  have hstableStandard : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  have hnormalizationPos : ∀ n : ℕ, 0 < n → 0 < normalization' n :=
    hscale.stableNorming.1
  have htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization' n)) :=
    FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOAstandard hnormalizationPos
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  let hgenerated := exists_generatedStableProcess_escapeRate_of_tightSource
    hDOAstandard hstableStandard htight hcdf
  let P : ProbabilityMeasure (CadlagPath unitInterval ℝ) := Classical.choose hgenerated
  have hgeneratedSpec := Classical.choose_spec hgenerated
  let hP : IsStableClockProcessLaw 2 (gaussianReal 0 1) UnitInterval.clock
      (P : Measure (CadlagPath unitInterval ℝ)) := Classical.choose hgeneratedSpec
  have hgeneratedSpec' := Classical.choose_spec hgeneratedSpec
  let Cgen : ℝ := Classical.choose hgeneratedSpec'
  have hEscapeGen : HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
        Measure (CadlagPath unitInterval ℝ)) Cgen := Classical.choose_spec hgeneratedSpec'
  let hX := iidUnitPathBlockProcess_isStableLevyProcess hP
  have hCgen : Cgen = -(Real.pi ^ 2) / 8 :=
    HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscapeGen hX canonicalMogulskiiScale
  have hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
        Measure (CadlagPath unitInterval ℝ)) (-(Real.pi ^ 2) / 8) := by
    simpa only [hCgen] using hEscapeGen
  have hslow := hDOAstandard.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have hdenom : Tendsto (probabilityRateDenominator 2 ν scale) atTop atBot :=
    sourceProbabilityRateDenominator_tendsto_atBot hscale (by norm_num) (by norm_num) hslow
  let Csource : ℝ := (-(Real.pi ^ 2) / 8) / d
  have hCnegative : -(Real.pi ^ 2) / 8 < 0 := by
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hconstant : d * Csource = -(Real.pi ^ 2) / 8 := by
    dsimp [Csource]
    field_simp [hd.ne']
  have hCsource : Csource < 0 := by
    dsimp [Csource]
    exact div_neg_of_neg_of_pos hCnegative hd
  have hdCsource : d * Csource < 0 := by rw [hconstant]; exact hCnegative
  have hκ : 0 < rateCoefficient 2 (d * Csource) := rateCoefficient_pos hdCsource
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator 2 ν scale
  have hStepRate : ∀ c : ContinuousAdmissibleStepCorridor,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet} (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) / denominator n)
        atTop (𝓝 (rateCoefficient 2 (d * Csource) *
          (ContinuousAdmissibleStepCorridor.energy 2 c).toReal)) := by
    intro c
    have hrate := sourceNormalizedStepCorridor_admissibleStepCorridor_rate
      hscale (by norm_num) (by norm_num) hslow hEscape hX hcdf hDOAstandard htight c
    simpa [paths, denominator, hconstant] using hrate
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet} (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) / denominator n)
        atTop (𝓝 (rateCoefficient 2 (d * Csource) * C₃.realEnergy)) := by
    intro C₃
    let hpieces := fun i : Fin C₃.count => hStepRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by
        simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, by simpa [denominator] using h.2.2⟩
  refine {
    variance := v
    spatialFactor := q
    timeFactor := d
    sourceEscapeConstant := Csource
    variance_pos := hvR
    sourceLaw_eq_gaussian := hμ
    scale_tendsto_atTop := hsmall.tendsto_atTop
    spatialFactor_pos := hq
    spatialVariance_eq_one := hqvariance
    timeFactor_eq_spatial_sq := hdq
    timeFactor_eq_inv_variance := rfl
    timeFactor_pos := hd
    sourceEscapeConstant_neg := hCsource
    normalizedEscape_eq := hconstant
    denominator_tendsto_atBot := hdenom
    finiteCorridorUnionRate := ?_
  }
  intro C₃
  simpa [paths, denominator] using hFiniteUnionRate C₃

namespace RawNormalSourceRateData

/-- A named source-rate record supplies the relative inner and outer rates for
every target with a vanishing energy-gap approximation. -/
theorem relativePathClassRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {scale : ℕ → ℝ} (data : RawNormalSourceRateData ν μ scale)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G) :
    ∃! H : ℝ, HasSourceRelativePathClassRate (ν := ν) 2 scale G
      (rateCoefficient 2 (data.timeFactor * data.sourceEscapeConstant)) H := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator 2 ν scale
  let κ : ℝ := rateCoefficient 2 (data.timeFactor * data.sourceEscapeConstant)
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using data.denominator_tendsto_atBot
  have hconstant : data.timeFactor * data.sourceEscapeConstant =
      -(Real.pi ^ 2) / 8 := data.normalizedEscape_eq
  have hdCsource : data.timeFactor * data.sourceEscapeConstant < 0 := by
    rw [hconstant]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hκ : 0 < κ := rateCoefficient_pos hdCsource
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)) := by
    intro C₃
    simpa [paths, denominator, κ] using data.finiteCorridorUnionRate C₃
  change ∃! H : ℝ,
    HasSourceRelativePathClassRate (ν := ν) 2 scale G κ H
  simpa [HasSourceRelativePathClassRate, paths, denominator, κ] using
    existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths Skorokhod.terminalLeftPathSpace hpaths denominator
      hdenom hκ hG hFiniteUnionRate

end RawNormalSourceRateData

/-- A centered finite-variance source with unit variance satisfies the raw
normal-source hypotheses through the existing Gaussian domain-of-attraction
theorem. This is the source-only form of the unit-variance normal branch. -/
noncomputable def rawNormalSourceRateData_of_centered_unitVariance
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1) :
    RawNormalSourceRateData ν (gaussianReal 0 1) scale := by
  have hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν := by
    rw [hvariance]
    norm_num
  have hDOA0 :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hcentered hsquare hsecondMoment
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt n) (fun _ => 0) := by
    simpa [hvariance, mul_one] using hDOA0
  have hStable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  exact rawNormalSourceRateData_of_rawSource hsmall hStable hDOA

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
