/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Basic
public import MeasureTheory.Measure.InnerMeasure
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.CDF
public import Mathlib.Topology.UnitInterval
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Approximation
public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic
public import Probability.Process.RandomWalk.Path.Representation.Cadlag
public import Probability.Process.RandomWalk.Path.Skorokhod.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClass.Rate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
public import Probability.Process.Stable.Levy
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
public import Probability.Sequence.IID.Basic
public import Topology.Cadlag.Basic
public import Probability.MeasureTheory.Asymptotics.SmallDeviation

import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Partition.Limit

/-!
# Discrete path-class rates for inner and outer probabilities

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discreteStepCorridorRates`:
  under the stable two-scale normalization with $0<\alpha\le2$, a slowly
  varying correction, a stable-process escape rate, the increment-law
  attraction and tightness hypotheses, and a vanishing-energy-gap corridor
  approximation for $G$, there is a unique common corridor energy $H>0$ such
  that, writing $E_n(G)=\{\omega:\operatorname{normalizedStepCadlagPathIcc}
  (\mathrm{scale},n,\omega)\in G\}$ and
  $d_n=\operatorname{probabilityRateDenominator}(\alpha,\nu,\mathrm{scale},n)$,
  $$
  \frac{\log (\mathbb P_\nu)_{*}(E_n(G))}{d_n},\qquad
  \frac{\log \mathbb P_\nu(E_n(G))}{d_n}
  \longrightarrow \operatorname{smallDeviationEnergyCoefficient}(\alpha,C)H.
  $$
  Here $(\mathbb P_\nu)_{*}$ is the inner measure for the i.i.d. sequence
  law, and $H$ is the common energy of the finite-corridor approximations.

This is the discrete path-class form of Theorem 1, equation (15), of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, bibliography key
`doi:10.1137/1119081`. Its exponent-two Gaussian specialization is Theorem 3,
Section 4, p. 764, of A. A. Mogul'skii's “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- The discrete `M₂` corridor rates imply the common logarithmic rate for the
inner and outer probabilities of a source-class `M` path set. Under the stable
two-scale, slowly varying, domain-of-attraction, tightness, and escape-rate
hypotheses, every vanishing-energy-gap approximation yields the same unique
energy $H>0$, and both logarithmic probabilities divided by
`probabilityRateDenominator α ν scale n` tend to
`smallDeviationEnergyCoefficient α C * H`. This is the discrete path-class form of A. A.
Mogul'skii's Theorem 1, equation (15); for $\alpha=2$ it gives the Gaussian
path-class rate in Theorem 3, Section 4, p. 764. See “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765, and its English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discreteStepCorridorRates
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    ∃! H : ℝ,
      ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto
          (fun n : ℕ => Real.log
            (((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (smallDeviationEnergyCoefficient α C * H)) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (smallDeviationEnergyCoefficient α C * H)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.normalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := smallDeviationEnergyCoefficient α C

  have hκ : 0 < κ := smallDeviationEnergyCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using probabilityRateDenominator_tendsto_atBot
      hscale hα hα₂ hslow
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n :=
    stableSmallDeviationRate_pos_eventually hscale hslow

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
    have hdiscrete := tendsto_scaledLog_normalizedStepCorridor_eq_energyRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
    have hEvent (n : ℕ) :
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet} =
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              corridorSet c.upper c.lower} := by
      ext increment
      simp [paths, ContinuousAdmissibleStepCorridor.toSet, FiniteStepCorridor.toSet]
    have hnull : ∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν) := by
      intro n
      exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
        c (iidSequenceLaw ν) (paths n) (by
          dsimp [paths]
          exact RandomWalk.measurable_normalizedStepCadlagPathIcc scale n
            |>.aemeasurable)
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal := by
      filter_upwards [hdiscrete.1] with n hn
      rw [hEvent n]
      exact ENNReal.toReal_pos (ne_of_gt hn) (measure_ne_top _ _)
    have hlograte : Tendsto (fun n : ℕ =>
        stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)
        atTop (𝓝 (C * 2 ^ α * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
      have h := hdiscrete.2
      have heq : (fun n : ℕ => stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) =ᶠ[atTop]
          (fun n : ℕ => stableSmallDeviationRate α ν scale n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
                  corridorSet c.upper c.lower}).toReal) := by
        filter_upwards [] with n
        simp [hEvent n]
      exact h.congr' heq
    have hratio : Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
      have heq : (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
              denominator n) =ᶠ[atTop]
          (fun n : ℕ => -(stableSmallDeviationRate α ν scale n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) := by
        filter_upwards [hratePos] with n hrate
        have hrateNe : stableSmallDeviationRate α ν scale n ≠ 0 := hrate.ne'
        dsimp [denominator, probabilityRateDenominator]
        field_simp [hrateNe]
      have hneg := hlograte.neg
      have htarget : -(C * 2 ^ α * (ContinuousAdmissibleStepCorridor.energy α c).toReal) =
          κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal := by
        dsimp [κ, smallDeviationEnergyCoefficient]
        ring
      simpa [htarget] using hneg.congr' heq.symm
    exact ⟨hnull, hpositive, hratio⟩

  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
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
    have hpieces := fun i : Fin C₃.count => hStepCorridorRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by
        simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, h.2.2⟩

  have hUnique := existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation
    (iidSequenceLaw ν) paths denominator hdenom hκ hG hFiniteUnionRate
  obtain ⟨A, hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate,
      hEnergyBounds⟩ :=
    exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths denominator hdenom hκ hG hFiniteUnionRate
  let H : ℝ := hLimits.commonEnergy
  refine ⟨H, ?_, ?_⟩
  · refine ⟨A, hLimits, rfl, hInnerPos, hOuterPos, hEnergyBounds.1,
      hEnergyBounds.2, ?_, ?_⟩
    · simpa [paths, denominator, κ, H] using hInnerRate
    · simpa [paths, denominator, κ, H] using hOuterRate
  · intro H' hH'
    obtain ⟨A', hLimits', hEq', _hInnerPos', _hOuterPos', _hPosRate',
      _hEnergyUpper', _hInnerRate', _hOuterRate'⟩ := hH'
    have hEq := hUnique.unique ⟨A', hLimits', hEq'⟩ ⟨A, hLimits, rfl⟩
    exact hEq

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
