/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.TerminalLeft.PathClass.Rate
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.MeasureTheory.Asymptotics.SmallDeviation

/-! # Relative path-class rates for terminal-left random walks

## Public declarations

The public theorem is
`existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscreteStepCorridorRates`.
For a target $G$ approximable by $M_3$ corridors relative to the
terminal-left path space, write
$E_n(G)=\{z:\mathbb N\to\mathbb R\mid
\mathrm{terminalLeftNormalizedStepCadlagPathIcc}(\mathrm{scale},n,z)\in G\}$ and
$D_n=\mathrm{probabilityRateDenominator}(\alpha,\nu,\mathrm{scale},n)$.
Let $\mathbb P_n=\mathrm{iidSequenceLaw}(\nu)$. The theorem supplies a
unique energy $H$ with eventual positivity and

$$
\frac{\log((\mathbb P_n.\mathrm{innerMeasure}(E_n(G))).\mathrm{toReal})}{D_n},\quad
\frac{\log((\mathbb P_n(E_n(G))).\mathrm{toReal})}{D_n}
\longrightarrow \operatorname{smallDeviationEnergyCoefficient}(\alpha,C)H,
\qquad D_n=\mathrm{probabilityRateDenominator}(\alpha,\nu,\mathrm{scale},n).
$$

The terminal-left path law is supported on the terminal-left path space; this
support lets the theorem use approximation relative to that path space.
This is the relative path-class form of Theorem 1, equation (15) of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- Every relatively `M` set in the terminal-left path space has a
unique common logarithmic rate for its inner and outer probabilities along the
terminal-left normalized random walk. No measurability assumption on the target set
is needed. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscreteStepCorridorRates
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
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation α terminalLeftPathSpace G) :
    ∃! H : ℝ,
      ∃ A : RelativeFiniteCorridorUnionApproximation α terminalLeftPathSpace G,
        ∃ hLimits : RelativeFiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy ∧
          (∀ᶠ n : ℕ in atTop,
            0 < ((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
          Tendsto
            (fun n : ℕ => Real.log
              (((iidSequenceLaw ν).innerMeasure
                {increment : ℕ → ℝ |
                  RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
            atTop (𝓝 (smallDeviationEnergyCoefficient α C * H)) ∧
          Tendsto
            (fun n : ℕ => Real.log
              ((iidSequenceLaw ν
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
  have hpaths : ∀ n increment, paths n increment ∈ terminalLeftPathSpace := by
    intro n increment
    exact terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
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
    let hpieces := fun i : Fin C₃.count => hStepCorridorRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, h.2.2⟩
  obtain ⟨H, hH, hUnique⟩ :=
    existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths terminalLeftPathSpace hpaths denominator hdenom hκ hG hFiniteUnionRate
  refine ⟨H, ?_, hUnique⟩
  obtain ⟨A, hLimits, rfl, hInnerPos, hOuterPos, hInnerRate, hOuterRate⟩ := hH
  refine ⟨A, hLimits, rfl, hInnerPos, hOuterPos, ?_, ?_⟩
  · simpa [paths, denominator, κ] using hInnerRate
  · simpa [paths, denominator, κ] using hOuterRate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
