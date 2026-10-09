/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.InnerOuter
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.ContinuousBoundary
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative

/-!
# Continuous-boundary rates from finite-corridor rates

This module lifts a finite-corridor-union rate family to continuous boundary
corridors. The result is independent of any particular source of those rates.
It gives inner and outer measure conclusions without measurability of the
target; ordinary probability follows when the target preimages are
null-measurable.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

open Skorokhod.PathClass.StepCorridor

/-- Finite-corridor-union rates imply the continuous-boundary inner and outer
rates. The common energy is identified with the reciprocal-width integral. -/
theorem tendsto_inner_outer_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ}
    (paths : ℕ → Ω → CadlagPath unitInterval ℝ)
    (denominator : ℕ → ℝ)
    (hdenom : Tendsto denominator atTop atBot) (hκ : 0 < κ)
    (hpaths : ∀ n ω, paths n ω ∈ Skorokhod.terminalLeftPathSpace)
    (hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
      (∀ n : ℕ, NullMeasurableSet {ω | paths n ω ∈ C₃.toSet} P) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (P {ω | paths n ω ∈ C₃.toSet}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log ((P {ω | paths n ω ∈ C₃.toSet}).toReal) /
          denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)))
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    (∀ᶠ n : ℕ in atTop,
      0 < (P.innerMeasure
        {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    (∀ᶠ n : ℕ in atTop,
      0 < (P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((P.innerMeasure
          {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            denominator n)
      atTop (𝓝 (κ * ∫ t : unitInterval,
        continuousBoundaryDensity α lower upper t ∂volume)) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
          denominator n)
      atTop (𝓝 (κ * ∫ t : unitInterval,
        continuousBoundaryDensity α lower upper t ∂volume)) := by
  obtain ⟨A, L, henergy⟩ :=
    exists_continuousBoundary_relativeApproximation_commonEnergy_eq_integral
      α lower upper hwidth hstartLower hstartUpper
  have hresult :=
    tendsto_inner_outer_log_probability_ratio_of_RelativeFiniteCorridorUnionApproximation
      P paths Skorokhod.terminalLeftPathSpace hpaths denominator hdenom hκ A
      hFiniteUnionRate
  obtain ⟨hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate, _hBounds⟩ := hresult
  have hlimitEq : hLimits.innerLimit = L.innerLimit :=
    tendsto_nhds_unique hLimits.inner_tendsto L.inner_tendsto
  have hcommonEnergy : hLimits.commonEnergy =
      ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume := by
    calc
      hLimits.commonEnergy = hLimits.innerLimit := rfl
      _ = L.innerLimit := hlimitEq
      _ = L.commonEnergy := rfl
      _ = ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume := henergy
  refine ⟨hInnerPos, hOuterPos, ?_, ?_⟩
  · simpa [hcommonEnergy] using hInnerRate
  · simpa [hcommonEnergy] using hOuterRate

/-- If the target preimages are null-measurable, the inner and outer rates
identify with the ordinary probability rate. -/
theorem tendsto_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ}
    (paths : ℕ → Ω → CadlagPath unitInterval ℝ)
    (denominator : ℕ → ℝ)
    (hdenom : Tendsto denominator atTop atBot) (hκ : 0 < κ)
    (hpaths : ∀ n ω, paths n ω ∈ Skorokhod.terminalLeftPathSpace)
    (hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
      (∀ n : ℕ, NullMeasurableSet {ω | paths n ω ∈ C₃.toSet} P) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (P {ω | paths n ω ∈ C₃.toSet}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log ((P {ω | paths n ω ∈ C₃.toSet}).toReal) /
          denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)))
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥)
    (hnull : ∀ n : ℕ, NullMeasurableSet
      {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper} P) :
    (∀ᶠ n : ℕ in atTop,
      0 < (P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
          denominator n)
      atTop (𝓝 (κ * ∫ t : unitInterval,
        continuousBoundaryDensity α lower upper t ∂volume)) := by
  obtain ⟨hInnerPos, _hOuterPos, hInnerRate, _hOuterRate⟩ :=
    tendsto_inner_outer_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
      P paths denominator hdenom hκ hpaths hFiniteUnionRate
      lower upper hwidth hstartLower hstartUpper
  have hmeasureEq : ∀ n : ℕ,
      P.innerMeasure
        {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper} =
      P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper} := by
    intro n
    exact innerMeasure_eq_measure_of_nullMeasurableSet P (hnull n)
  have hprobPos : ∀ᶠ n : ℕ in atTop,
      0 < (P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal := by
    filter_upwards [hInnerPos] with n hn
    simpa [hmeasureEq n] using hn
  have hprobRate : Tendsto
      (fun n : ℕ => Real.log
        ((P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
          denominator n)
      atTop (𝓝 (κ * ∫ t : unitInterval,
        continuousBoundaryDensity α lower upper t ∂volume)) := by
    have heq : (fun n : ℕ => Real.log
        ((P {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
          denominator n) =
        (fun n : ℕ => Real.log
          ((P.innerMeasure
            {ω | paths n ω ∈ relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            denominator n) := by
      funext n
      rw [← hmeasureEq n]
    rw [heq]
    exact hInnerRate
  exact ⟨hprobPos, hprobRate⟩

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
