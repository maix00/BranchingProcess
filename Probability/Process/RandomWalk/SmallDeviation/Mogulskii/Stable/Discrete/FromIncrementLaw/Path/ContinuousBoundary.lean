/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Stable.Domain
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.ContinuousBoundary
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.ContinuousBoundary
public import Probability.MeasureTheory.Asymptotics.SmallDeviation

/-!
# Continuous-boundary Mogul'skii rates from increment laws

This module specializes the raw-domain-of-attraction path-class rate to a
strictly separated continuous corridor. Its energy is the real integral of
the reciprocal width to the power `α`. The general result is formulated with
inner and outer measures. The finite-step source event is shown measurable,
so the ordinary-probability corollary needs no caller-supplied measurability
condition.

For $E(t)=u(t)-l(t)>0$, the rate functional is
\[
 I_\alpha(l,u)=\int_0^1 E(t)^{-\alpha}\,dt.
\]
For
$A_n=\{\xi:\texttt{terminalLeftNormalizedStepCadlagPathIcc}(s,n,\xi)
\in\texttt{relativeContinuousBoundaryCorridorSet}(l,u)\}$, put
$p_n^{\rm in}=((\operatorname{iidSequenceLaw}(\nu)).\operatorname{innerMeasure}
A_n).\operatorname{toReal}$ and
$p_n^{\rm out}=\operatorname{iidSequenceLaw}(\nu)(A_n).\operatorname{toReal}$.
Under the raw domain-of-attraction hypotheses, both probabilities have
logarithmic rate
\[
 \frac{\log p_n^{\rm in}}{D_n},\quad
 \frac{\log p_n^{\rm out}}{D_n}\longrightarrow
 \operatorname{smallDeviationEnergyCoefficient}(\alpha,dC_{\rm source})
 I_\alpha(l,u),
 \qquad D_n=\operatorname{probabilityRateDenominator}(\alpha,\nu,s,n),
\]
with eventual positivity; the theorem records the inner-measure limit as
well when measurability of the limiting path class is unavailable.

## Public declarations

- `exists_source_continuousBoundary_inner_outer_rates_of_rawSource`: for the
  finite-step corridor event $A_n$, the inner and outer probabilities are
  eventually positive and satisfy the two limits displayed above.
- `exists_source_continuousBoundary_probability_rate_of_rawSource`: the same
  limit holds for $\mathbb P_\nu(A_n)$ because the finite-step event is
  measurable.

This is the continuous-boundary specialization of the $0<\alpha<2$ case of
Theorem 1, equation (15), of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open Skorokhod.PathClass.StepCorridor

/-- The continuous-corridor rate from raw domain-of-attraction inputs, with its limiting
energy identified as the reciprocal-width integral. No measurability of the
target path set is assumed, so the conclusion records inner and outer rates. -/
theorem exists_source_continuousBoundary_inner_outer_rates_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ,
      0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < ((iidSequenceLaw ν).innerMeasure
          {increment : ℕ → ℝ |
            RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          (((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) ∧
      Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) := by
  obtain ⟨d, Csource, hd, hCsource, hdenom, hFiniteUnionRate⟩ :=
    exists_source_finiteCorridorUnion_rates_of_rawSource
      hsmall hStable hDOA hcdf hα₀ hα₂ hcenter
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := smallDeviationEnergyCoefficient α (d * Csource)
  have hdCsource : d * Csource < 0 := mul_neg_of_pos_of_neg hd hCsource
  have hκ : 0 < κ := smallDeviationEnergyCoefficient_pos hdCsource
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
  have hFiniteUnionRate' : ∀ C₃ : FiniteCorridorUnion α,
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
    simpa [paths, denominator, κ] using hFiniteUnionRate C₃
  obtain ⟨hInnerPos, hOuterPos, hInnerRate, hOuterRate⟩ :=
    ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.tendsto_inner_outer_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
      (iidSequenceLaw ν) paths denominator hdenom hκ hpaths hFiniteUnionRate'
      lower upper hwidth hstartLower hstartUpper
  refine ⟨d, Csource, hd, hCsource, ?_, ?_, ?_, ?_⟩
  · simpa [paths] using hInnerPos
  · simpa [paths] using hOuterPos
  · simpa [paths, denominator, κ] using hInnerRate
  · simpa [paths, denominator, κ] using hOuterRate

/-- The source corridor preimages are measurable on the finite-step
increment space, so the inner and outer conclusions identify with ordinary
event probabilities. -/
theorem exists_source_continuousBoundary_probability_rate_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ,
      0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) := by
  obtain ⟨d, Csource, hd, hCsource, hInnerPos, _hOuterPos,
      hInnerRate, _hOuterRate⟩ :=
    exists_source_continuousBoundary_inner_outer_rates_of_rawSource
      hsmall hStable hDOA hcdf hα₀ hα₂ hcenter lower upper hwidth hstartLower hstartUpper
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment
  have hnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ | paths n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} (iidSequenceLaw ν) := by
    intro n
    exact (RandomWalk.measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
      lower upper scale n).nullMeasurableSet
  have hmeasureEq : ∀ n : ℕ,
      (iidSequenceLaw ν).innerMeasure
        {increment : ℕ → ℝ | paths n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper} =
      iidSequenceLaw ν {increment : ℕ → ℝ | paths n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} := by
    intro n
    exact innerMeasure_eq_measure_of_nullMeasurableSet (iidSequenceLaw ν) (hnull n)
  have hprobPos : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν {increment : ℕ → ℝ | paths n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper}).toReal := by
    filter_upwards [hInnerPos] with n hn
    simpa [paths, hmeasureEq n] using hn
  have hprobRate : Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν {increment : ℕ → ℝ | paths n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n)
      atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) *
        ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) := by
    have heq : (fun n : ℕ => Real.log
        ((iidSequenceLaw ν {increment : ℕ → ℝ | paths n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n) =
        (fun n : ℕ => Real.log
          (((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ | paths n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator α ν scale n) := by
      funext n
      rw [← hmeasureEq n]
    rw [heq]
    simpa [paths] using hInnerRate
  exact ⟨d, Csource, hd, hCsource, hprobPos, hprobRate⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
