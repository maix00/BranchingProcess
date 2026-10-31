/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClass.Rate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.TerminalLeft.Partition.Limit
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation
public import Probability.MeasureTheory.Asymptotics.SmallDeviation

/-!
# Path-class rates for the terminal-left endpoint convention

## Public declarations

The terminal-left path records the partial sums through `n - 1`. This file transfers
the exact terminal-left normalized `M₂` corridor rates to the general `M` class using
the shared finite-union and approximation theorems.

The path-class rate formalizes A. A. Mogul'skii's Theorem 1, equation (15),
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081.

Let $Y_n^\xi=\texttt{terminalLeftNormalizedStepCadlagPathIcc}(s,n,\xi)$,
$d_n=-1/\rho_n$ for the stable small-deviation rate $\rho_n$, and
$P_n(G)=(\operatorname{iidSequenceLaw}\nu)\{\xi:Y_n^\xi\in G\}$. The
declarations in `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete`
are:

- `terminalLeftNormalizedStepCorridor_admissibleStepCorridor_rate`: for a
  continuous admissible step corridor $c$, its terminal-left path event is
  null-measurable, has positive probability eventually, and
  $\log P_n(c.\texttt{toSet})/d_n\to
  \operatorname{smallDeviationEnergyCoefficient}(\alpha,C)(c.\operatorname{energy}(\alpha)).\operatorname{toReal}$.
- `tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscreteStepCorridorRates`:
  for a null-measurable source-class target $G$ with a vanishing energy-gap
  approximation, there is a unique common approximation energy $H$ and
  $\log P_n(G)/d_n\to\operatorname{smallDeviationEnergyCoefficient}(\alpha,C)H$.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- Under the terminal-left endpoint convention, every finite-partition `M₂`
corridor has the exact logarithmic rate. The event is null-measurable by the
measurable terminal-left path map and the general path-space corridor result. -/
theorem terminalLeftNormalizedStepCorridor_admissibleStepCorridor_rate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : ContinuousAdmissibleStepCorridor) :
    (∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}
      (iidSequenceLaw ν)) ∧
    (∀ᶠ n : ℕ in atTop, 0 < (iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal) ∧
    Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal) /
        probabilityRateDenominator α ν scale n)
      atTop (𝓝 (smallDeviationEnergyCoefficient α C * (c.energy α).toReal)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment
  have hdiscrete := tendsto_scaledLog_terminalLeftNormalizedStepCorridor_eq_energyRate
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
  have hEvent (n : ℕ) :
      {increment : ℕ → ℝ | paths n increment ∈ c.toSet} =
        {increment : ℕ → ℝ |
          RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
            corridorSet c.upper c.lower} := by
    ext increment
    simp [paths, ContinuousAdmissibleStepCorridor.toSet, FiniteStepCorridor.toSet]
  have hnull : ∀ n : ℕ,
      NullMeasurableSet {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν) := by
    intro n
    exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
      c (iidSequenceLaw ν) (paths n) (by
        dsimp [paths]
        exact RandomWalk.measurable_terminalLeftNormalizedStepCadlagPathIcc scale n
          |>.aemeasurable)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal := by
    filter_upwards [hdiscrete.1] with n hn
    rw [hEvent n]
    exact ENNReal.toReal_pos (ne_of_gt hn) (measure_ne_top _ _)
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n :=
    stableSmallDeviationRate_pos_eventually hscale hslow
  have hlograte : Tendsto (fun n : ℕ => stableSmallDeviationRate α ν scale n *
      Real.log ((iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal))
      atTop (𝓝 (C * 2 ^ α * (c.energy α).toReal)) := by
    have heq : (fun n : ℕ => stableSmallDeviationRate α ν scale n *
        Real.log ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) =ᶠ[atTop]
        (fun n : ℕ => stableSmallDeviationRate α ν scale n *
          Real.log (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
                corridorSet c.upper c.lower}).toReal) := by
      filter_upwards [] with n
      simp [hEvent n]
    exact hdiscrete.2.congr' heq
  have hratio : Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
      {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
        probabilityRateDenominator α ν scale n)
      atTop (𝓝 (smallDeviationEnergyCoefficient α C * (c.energy α).toReal)) := by
    have heq : (fun n : ℕ => Real.log ((iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
          probabilityRateDenominator α ν scale n) =ᶠ[atTop]
        fun n => -(stableSmallDeviationRate α ν scale n *
          Real.log ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) := by
      filter_upwards [hratePos] with n hrate
      have hrateNe : stableSmallDeviationRate α ν scale n ≠ 0 := hrate.ne'
      dsimp [probabilityRateDenominator]
      field_simp [hrateNe]
    have htarget : -(C * 2 ^ α * (c.energy α).toReal) =
        smallDeviationEnergyCoefficient α C * (c.energy α).toReal := by
      dsimp [smallDeviationEnergyCoefficient]
      ring
    exact by simpa [htarget] using hlograte.neg.congr' heq.symm
  exact ⟨hnull, ⟨hpositive, hratio⟩⟩

/-- The terminal-left endpoint convention has the random-walk Mogul'skii rate for
every null-measurable target in class `M`. The `M₃` and approximation
arguments are shared with the càdlàg path convention. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscreteStepCorridorRates
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}
      (iidSequenceLaw ν)) :
    (∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}
      (iidSequenceLaw ν)) ∧
    ∃! H : ℝ,
      (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy) ∧
      Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          probabilityRateDenominator α ν scale n)
        atTop (𝓝 (smallDeviationEnergyCoefficient α C * H)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := smallDeviationEnergyCoefficient α C
  have hκ : 0 < κ := smallDeviationEnergyCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using probabilityRateDenominator_tendsto_atBot
      hscale hα hα₂ hslow
  have hStepCorridorRate : ∀ c : ContinuousAdmissibleStepCorridor,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
    intro c
    simpa [paths, denominator, κ] using
      terminalLeftNormalizedStepCorridor_admissibleStepCorridor_rate hscale hα hα₂ hslow hEscape hX hcdf
        hDOA htightBase c
  refine ⟨?_, ?_⟩
  · intro n
    simpa [paths] using hGnull n
  · have hresult := tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stepCorridorRates
      (iidSequenceLaw ν) paths denominator hdenom hκ hG hGnull hStepCorridorRate
    simpa [paths, denominator, κ] using hresult.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
