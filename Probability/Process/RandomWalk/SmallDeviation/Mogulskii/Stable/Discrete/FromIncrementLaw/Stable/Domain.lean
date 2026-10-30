/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import MeasureTheory.Measure.InnerMeasure
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.RelativeApproximation
public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.Stable.Basic
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClass.Rate
public import Probability.Sequence.IID.Basic
public import Topology.Cadlag.Basic
public import Topology.Cadlag.Skorokhod.Path.TerminalLeft
public import Probability.MeasureTheory.Asymptotics.SmallDeviation

import Probability.Distributions.Scaling
import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.Subsequence
import Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness.Result
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Stable.Normalization
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.TerminalLeft.PathClass.Relative
import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.EscapeRate
import Probability.Process.Stable.PathLaw.FullProcess
import Probability.Process.Stable.PathLaw.Concatenation
import Probability.Process.Stable.PathLaw.MonotoneGrid
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.ContinuousBoundary
import all Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness.Basic
import Probability.Distributions.Stable.Gaussian.Basic

import Probability.Distributions.DomainOfAttraction.Centering
import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Centering

/-!
# Stable Mogul'skii interface from increment laws

The stable-process path law used by the rate construction is obtained from
the random-walk domain-of-attraction limit. Tightness and finite-dimensional laws construct a
unit-interval stable path law; iid concatenation then supplies the full-time
stable Lévy process needed by the corridor-rate argument. Callers provide no
process witness or path-law witness.

## Public declarations

- `exists_source_finiteCorridorUnion_rates_of_rawSource`: for $0<\alpha<2$,
  constructs $d>0$ and $C_{\rm source}<0$ such that, for every finite
  corridor union $C_3$, the event
  $A_n(C_3)=\{\xi:\operatorname{terminalLeftNormalizedStepCadlagPathIcc}
  (\mathrm{scale},n,\xi)\in C_3.\mathrm{toSet}\}$ is null-measurable,
  eventually has positive probability, and
  $\frac{\log\mathbb P_\nu(A_n(C_3))}{D_n}\to
  \operatorname{smallDeviationEnergyCoefficient}(\alpha,dC_{\rm source})\,
  \operatorname{realEnergy}(C_3)$, where
  $D_n=\operatorname{probabilityRateDenominator}(\alpha,\nu,\mathrm{scale},n)$.
- `HasSourceRelativePathClassRate`: records a common energy $H$ and eventual
  positivity of the inner and outer probabilities of a source path-class
  event $A_n(G)=\{\xi:\operatorname{terminalLeftNormalizedStepCadlagPathIcc}
  (\mathrm{scale},n,\xi)\in G\}$, together with
  $\frac{\log (\mathbb P_\nu)_*(A_n(G))}{D_n}\to\kappa H$ and
  $\frac{\log\mathbb P_\nu(A_n(G))}{D_n}\to\kappa H$.
- `exists_source_relative_pathClass_rates_of_rawSource`: for every target
  $G$ with a relative vanishing-energy-gap approximation, produces the same
  source constants and a unique $H$ satisfying
  `HasSourceRelativePathClassRate` with
  $\kappa=\operatorname{smallDeviationEnergyCoefficient}(\alpha,dC_{\rm source})$.

The resulting stable-domain path rate formalizes the `0 < α < 2` branch of
Theorem 1 in A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- Regularly varying tails and the applicable centering condition give the
J₁ tightness required by the subsequential path-law construction. The index
one condition is supplied in the original raw normalization and transferred
through the same reindexing used below. -/
private lemma exists_rawSource_reindexed_tightInputs
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization) :
    ∃ d q : ℝ, 0 < d ∧ q = d ^ (1 / α) ∧ 0 < q ∧
      ∃ m : ℕ → ℕ,
        (∀ n, 0 < m n) ∧
        Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (𝓝 d⁻¹) ∧
        ∃ normalization' : ℕ → ℝ,
          IsStableMogulskiiScale α ν normalization' scale ∧
          normalization' =ᶠ[atTop] (fun n => normalization (m n)) ∧
          ∃ hmap : IsProbabilityMeasure (μ.map fun x => q * x),
            IsStrictlyAlphaStable α (μ.map fun x => q * x) ∧
            @IsInDomainOfAttractionAlong ν (μ.map fun x => q * x)
              inferInstance hmap normalization' (fun _ => 0) ∧
            IsTightMeasureSet (Set.range
              (fun n => RandomWalk.normalizedStepPathLaw ν normalization' n)) := by
  obtain ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale',
      heq, hmap, hStable', hDOA'⟩ :=
    exists_source_reindexed_mogulskii_data hsmall hStable hDOA hα₂
  let : IsProbabilityMeasure (μ.map fun x => q * x) := hmap
  have hlimit : IsAlphaStable α (μ.map fun x => q * x) := hStable'.isAlphaStable
  have htail := hDOA'.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization' n)) := by
    by_cases hαone : α = 1
    · have hcenterRaw : IsMogulskiiIndexOneCentered ν normalization := by
        rcases hcenter with hne | hc
        · exact (hne hαone).elim
        · exact hc
      have hcenter' := IsMogulskiiIndexOneCentered.of_reindexedNorming
        hd m hmratio hmPos heq hcenterRaw
      have hnormOne : IsStableNorming 1 ν normalization' := by
        simpa [hαone] using hscale'.stableNorming
      have htailOne : Asymptotics.IsRegularlyVaryingAtTop
          (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1) := by
        simpa [hαone] using htail
      exact FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
        hnormOne htailOne hcenter'
    · rcases lt_or_gt_of_ne hαone with hlt | hgt
      · exact FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
          hscale'.stableNorming hα₀ hlt htail
      · have hint : Integrable (fun x : ℝ => x) ν :=
          integrable_id_of_twoSidedTail_regularlyVarying hgt htail
        have hmean := hDOA'.integral_eq_zero_of_index_gt_one
          hlimit hscale'.stableNorming hgt hα₂
        exact FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
          hscale'.stableNorming hα₀ hgt hα₂ htail hint hmean
  exact ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale', heq,
    hmap, hStable', hDOA', htight⟩

/-- Internal source construction for the relative Mogul'skii theorem. The raw
domain-of-attraction assumptions generate the path law, its full-time stable
process, and the escape rate. The index-one sine-centering condition is the
only regime-specific input. -/
private lemma exists_source_relative_pathClass_rates_with_generated_witness
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization) :
    ∃ d q Csource : ℝ,
      0 < d ∧ q = d ^ (1 / α) ∧ 0 < q ∧
      ∃ P : ProbabilityMeasure (CadlagPath unitInterval ℝ),
        ∃ hP : IsStableClockProcessLaw α (μ.map fun x => q * x)
          unitInterval.clock (P : Measure (CadlagPath unitInterval ℝ)),
        HasStableProcessEscapeRate α (μ.map fun x => q * x)
          ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
            Measure (CadlagPath unitInterval ℝ)) (d * Csource) ∧
        Csource < 0 ∧
        Tendsto (probabilityRateDenominator α ν scale) atTop atBot ∧
        (∀ C₃ : FiniteCorridorUnion α,
          (∀ n : ℕ, NullMeasurableSet
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}
            (iidSequenceLaw ν)) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) ∧
          Tendsto
            (fun n : ℕ => Real.log
              ((iidSequenceLaw ν
                {increment : ℕ → ℝ |
                  RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) /
                probabilityRateDenominator α ν scale n)
            atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) * C₃.realEnergy)))
        := by
  obtain ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale',
      heq, hmap, hStable', hDOA', htight⟩ :=
    exists_rawSource_reindexed_tightInputs hsmall hStable hDOA hα₀ hα₂ hcenter
  let : IsProbabilityMeasure (μ.map fun x => q * x) := hmap
  have hcdf' : 0 < cdf (μ.map fun x => q * x) 0 ∧
      cdf (μ.map fun x => q * x) 0 < 1 := by
    rw [cdf_map_mul (μ := μ) (r := q) (x := 0) hq, zero_div]
    exact hcdf
  obtain ⟨P, hP, Cq, hEscape⟩ :=
    ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_generatedStableProcess_escapeRate_of_tightSource
      hDOA' hStable' htight hcdf'
  let Csource : ℝ := Cq / d
  have hconstant : d * Csource = Cq := by
    dsimp [Csource]
    field_simp [hd.ne']
  have hsmallDeviationEnergyCoefficient : smallDeviationEnergyCoefficient α (d * Csource) =
      smallDeviationEnergyCoefficient α Cq := by
    rw [hconstant]
  have hEscape' : HasStableProcessEscapeRate α (μ.map fun x => q * x)
      ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
        Measure (CadlagPath unitInterval ℝ)) (d * Csource) := by
    simpa [hconstant] using hEscape
  let hX := iidUnitPathBlockProcess_isStableLevyProcess hP
  have hCsource : Csource < 0 := by
    dsimp [Csource]
    exact div_neg_of_neg_of_pos hEscape.negative hd
  have hdCsource : d * Csource < 0 := mul_neg_of_pos_of_neg hd hCsource
  have hslow := hDOA'.isSlowlyVarying_stableSlowVariation
    hStable'.isAlphaStable hα₀ hα₂
  have hdenom : Tendsto (probabilityRateDenominator α ν scale) atTop atBot :=
    probabilityRateDenominator_tendsto_atBot hscale' hα₀ (le_of_lt hα₂) hslow
  have hκ : 0 < smallDeviationEnergyCoefficient α (d * Csource) :=
    smallDeviationEnergyCoefficient_pos hdCsource
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
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
        atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) *
          (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
    intro c
    simpa [paths, denominator, hsmallDeviationEnergyCoefficient] using
      terminalLeftNormalizedStepCorridor_admissibleStepCorridor_rate
        hscale' hα₀ (le_of_lt hα₂) hslow hEscape hX hcdf' hDOA' htight c
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
        atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) * C₃.realEnergy)) := by
    intro C₃
    let hpieces := fun i : Fin C₃.count => hStepCorridorRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by
        simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, by
      simpa [denominator] using h.2.2⟩
  refine ⟨d, q, Csource, hd, hqEq, hq, P, hP, hEscape', hCsource,
    hdenom, ?_⟩
  intro C₃
  simpa [paths, denominator] using hFiniteUnionRate C₃

/-- From the raw stable domain-of-attraction hypotheses, construct the common
source normalization constants and prove the rates for every finite union of
admissible corridors. This is the finite-corridor input used by the general
path-class and continuous-boundary theorems. -/
theorem exists_source_finiteCorridorUnion_rates_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization) :
    ∃ d Csource : ℝ,
      0 < d ∧ Csource < 0 ∧
      Tendsto (probabilityRateDenominator α ν scale) atTop atBot ∧
      ∀ C₃ : FiniteCorridorUnion α,
        (∀ n : ℕ, NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}
          (iidSequenceLaw ν)) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) /
              probabilityRateDenominator α ν scale n)
          atTop (𝓝 (smallDeviationEnergyCoefficient α (d * Csource) * C₃.realEnergy)) := by
  obtain ⟨d, _q, Csource, hd, _hq, _hqPos, _P, _hP, _hEscape,
      hCsource, hdenom, hFiniteUnionRate⟩ :=
    exists_source_relative_pathClass_rates_with_generated_witness
      hsmall hStable hDOA hcdf hα₀ hα₂ hcenter
  exact ⟨d, Csource, hd, hCsource, hdenom, hFiniteUnionRate⟩

/-- A source path-class rate consists of a common corridor energy and the
corresponding logarithmic limits for the inner and outer probabilities. The
definition deliberately makes no measurability claim about the target set. -/
def HasSourceRelativePathClassRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (α : ℝ) (scale : ℕ → ℝ)
    (G : Set (CadlagPath unitInterval ℝ)) (κ H : ℝ) : Prop :=
  ∃ A : RelativeFiniteCorridorUnionApproximation α
      Skorokhod.terminalLeftPathSpace G,
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
        atTop (𝓝 (κ * H)) ∧
      Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (κ * H))

/-- Relative Mogul'skii theorem for `0 < α < 2`, derived from increment-law
domain-of-attraction assumptions generate the path law and stable-process
escape rate internally. For every relatively approximable target, the result
is stated as inner- and outer-measure rates; it makes no measurability claim
about the target event. -/
theorem exists_source_relative_pathClass_rates_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization) :
    ∃ d Csource : ℝ, 0 < d ∧ Csource < 0 ∧
      ∀ {G : Set (CadlagPath unitInterval ℝ)},
        HasRelativeVanishingEnergyGapApproximation α
          Skorokhod.terminalLeftPathSpace G →
        ∃! H : ℝ,
          HasSourceRelativePathClassRate (ν := ν) α scale G
            (smallDeviationEnergyCoefficient α (d * Csource)) H := by
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
  refine ⟨d, Csource, hd, hCsource, ?_⟩
  intro G hG
  change ∃! H : ℝ, HasSourceRelativePathClassRate (ν := ν) α scale G κ H
  simpa [HasSourceRelativePathClassRate, paths, denominator, κ] using
    existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths Skorokhod.terminalLeftPathSpace hpaths denominator
      hdenom hκ hG hFiniteUnionRate'

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
