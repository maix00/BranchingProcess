/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Realization
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.StableDomain
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
public import MeasureTheory.Measure.InnerOuter

/-!
# Source-only rates for arbitrary i.i.d. realizations

This module combines raw stable-domain inputs with the general realization
transfer. Callers provide the coordinate process, but finite-corridor rates
are obtained internally from the source theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- The relative path-class rate for a source random walk realized by an
arbitrary i.i.d. coordinate process. The record carries its normalization,
the common energy, and named inner/outer rate fields. -/
structure SourceIidRelativePathClassRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (α : ℝ) (scale : ℕ → ℝ) (coordinate : ℕ → Ω → ℝ)
    (G : Set (CadlagPath unitInterval ℝ)) where
  timeFactor : ℝ
  sourceEscapeConstant : ℝ
  energy : ℝ
  approximation : RelativeFiniteCorridorUnionApproximation α
    Skorokhod.terminalLeftPathSpace G
  energyLimits : RelativeFiniteCorridorUnionEnergyLimits approximation
  energy_eq : energy = energyLimits.commonEnergy
  timeFactor_pos : 0 < timeFactor
  sourceEscapeConstant_neg : sourceEscapeConstant < 0
  denominator_tendsto_atBot :
    Tendsto (probabilityRateDenominator α ν scale) atTop atBot
  innerPositive : ∀ᶠ n : ℕ in atTop,
    0 < (P.innerMeasure
      {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G}).toReal
  outerPositive : ∀ᶠ n : ℕ in atTop,
    0 < (P
      {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G}).toReal
  innerRate : Tendsto
    (fun n : ℕ => Real.log
      ((P.innerMeasure
        {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈ G}).toReal) /
        probabilityRateDenominator α ν scale n)
    atTop (𝓝 (rateCoefficient α (timeFactor * sourceEscapeConstant) * energy))
  outerRate : Tendsto
    (fun n : ℕ => Real.log
      ((P
        {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈ G}).toReal) /
        probabilityRateDenominator α ν scale n)
    atTop (𝓝 (rateCoefficient α (timeFactor * sourceEscapeConstant) * energy))

/-- Raw source assumptions produce the relative inner/outer rate for any
i.i.d. realization. The finite-corridor rates are derived internally; no
canonical-rate family is an input. -/
noncomputable def sourceIidRelativePathClassRate_of_rawSource
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation α
      Skorokhod.terminalLeftPathSpace G) :
    SourceIidRelativePathClassRate (ν := ν) P α scale coordinate G := by
  let hsource := exists_source_finiteCorridorUnion_rates_of_rawSource
    hsmall hStable hDOA hcdf hα₀ hα₂ hcenter
  let d : ℝ := Classical.choose hsource
  have hsourceD := Classical.choose_spec hsource
  let Csource : ℝ := Classical.choose hsourceD
  have hsourceFields := Classical.choose_spec hsourceD
  have hd : 0 < d := hsourceFields.1
  have hCsource : Csource < 0 := hsourceFields.2.1
  have hdenominator : Tendsto (probabilityRateDenominator α ν scale) atTop atBot :=
    hsourceFields.2.2.1
  have hFiniteCorridorRate := hsourceFields.2.2.2
  have hdCsource : d * Csource < 0 := mul_neg_of_pos_of_neg hd hCsource
  have hκ : 0 < rateCoefficient α (d * Csource) :=
    rateCoefficient_pos hdCsource
  have hcanonicalFiniteCorridorRate : ∀ C : FiniteCorridorUnion α,
      (∀ᶠ n : ℕ in atTop, 0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) * C.realEnergy)) := by
    intro C
    exact ⟨(hFiniteCorridorRate C).2.1, (hFiniteCorridorRate C).2.2⟩
  have hresult := existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_iid
    (P := P) (ν := ν) (α := α) (κ := rateCoefficient α (d * Csource))
    (g := probabilityRateDenominator α ν scale)
    hdenominator hκ hindep hmeasurable hlaw scale hcanonicalFiniteCorridorRate hG
  let H : ℝ := Classical.choose hresult
  have hH := (Classical.choose_spec hresult).1
  let A : RelativeFiniteCorridorUnionApproximation α
      Skorokhod.terminalLeftPathSpace G := Classical.choose hH
  have hA := Classical.choose_spec hH
  let hLimits : RelativeFiniteCorridorUnionEnergyLimits A := Classical.choose hA
  have hRates := Classical.choose_spec hA
  have hEnergyEq := hRates.1
  have hInnerPositive := hRates.2.1
  have hOuterPositive := hRates.2.2.1
  have hInnerRate := hRates.2.2.2.1
  have hOuterRate := hRates.2.2.2.2
  exact {
    timeFactor := d
    sourceEscapeConstant := Csource
    energy := H
    approximation := A
    energyLimits := hLimits
    energy_eq := hEnergyEq
    timeFactor_pos := hd
    sourceEscapeConstant_neg := hCsource
    denominator_tendsto_atBot := hdenominator
    innerPositive := hInnerPositive
    outerPositive := hOuterPositive
    innerRate := hInnerRate
    outerRate := hOuterRate }

/-- If the realized path-class event is null-measurable for every `n`, the
relative inner rate is the ordinary event-probability rate. This wrapper
states the measurability requirement explicitly. -/
theorem SourceIidRelativePathClassRate.probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α : ℝ} {scale : ℕ → ℝ} {coordinate : ℕ → Ω → ℝ}
    {G : Set (CadlagPath unitInterval ℝ)}
    (rates : SourceIidRelativePathClassRate (ν := ν) P α scale coordinate G)
    (hnull : ∀ n : ℕ, NullMeasurableSet
      {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} P) :
    (∀ᶠ n : ℕ in atTop,
      0 < (P
        {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈ G}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((P
          {ω | sourceNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈ G}).toReal) /
          probabilityRateDenominator α ν scale n)
      atTop (𝓝 (rateCoefficient α
        (rates.timeFactor * rates.sourceEscapeConstant) * rates.energy)) := by
  have heq (n : ℕ) : P.innerMeasure
      {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} =
      P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} :=
    innerMeasure_eq_measure_of_nullMeasurableSet P (hnull n)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < (P
        {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈ G}).toReal := by
    filter_upwards [rates.innerPositive] with n hn
    simpa [heq n] using hn
  have heqLog : (fun n : ℕ => Real.log
      ((P
        {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈ G}).toReal) /
        probabilityRateDenominator α ν scale n) =
      fun n : ℕ => Real.log
        ((P.innerMeasure
          {ω | sourceNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈ G}).toReal) /
          probabilityRateDenominator α ν scale n := by
    funext n
    rw [← heq n]
  rw [heqLog]
  exact ⟨hpositive, rates.innerRate⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
