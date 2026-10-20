/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path.Existence
public import Probability.Distributions.Stable.Attraction.Normal.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.EndpointBandTransfer.Lower.EndpointMass
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.EndpointBandTransfer.Lower.PathLimit

public import Probability.Distributions.Gaussian.Interval
/-!
# Fixed diffusive blocks from a generated Gaussian path law

Normal-domain path tightness constructs the Gaussian unit-interval path law.
Its associated Lévy process supplies the stable escape rate, and the variable-
block path limit transfers the endpoint-band mass to rounded diffusive blocks.

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.exists_eventually_diffusiveEndpointBandReturnBlockProbability_lower`:
  for centered unit-variance increments and any fixed finite family of
  interior endpoint bands, there is a diffusive block constant for which each
  band's return probability has a common positive eventual lower bound.

This is the finite-dimensional return-block input used in the proof of
Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- A centered unit-variance increment law admits a fixed diffusive block
constant for which all seven endpoint-return bands have a common positive
eventual lower bound. The Gaussian path law and its escape rate are generated
from the source law by normal-domain tightness. -/
theorem exists_eventually_diffusiveEndpointBandReturnBlockProbability_lower
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((-(Real.pi ^ 2) / 8 /
                (((upper - lower - 8 * epsilon) / 2) ^ (2 : ℝ)) - delta) * constant)) ≤
            iidSequenceLaw ν
              (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
                (epsilon * scale n) i
                (diffusiveBlockLength constant scale n)) := by
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  have hDOA : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0) := by
    simpa [normalization] using
      ProbabilityTheory.isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment
        ν hν
  have hnormalization : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have htight : IsTightMeasureSet (Set.range fun n =>
      RandomWalk.normalizedStepPathLaw ν normalization n) :=
    RandomWalk.FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hnormalization
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (by norm_num)
  obtain ⟨P, Q, X, hP, hX, hEscape⟩ :=
    Path.exists_gaussianStablePathLaw_with_escapeRate ν hν hscale
  letI : IsProbabilityMeasure (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) :=
    Q.property
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  let radius : ℝ := (upper - lower - 8 * epsilon) / 2
  let C : ℝ := -(Real.pi ^ 2) / 8
  obtain ⟨amplitude, hamplitude, hmass⟩ :=
    exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hbands
  let constant : ℝ := amplitude ^ (2 : ℝ)
  have hconstant : 0 < constant :=
    Real.rpow_pos_of_pos hamplitude 2
  let lowerBound : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    ((C / radius ^ (2 : ℝ) - delta) * constant))
  let length : ℕ → ℕ := diffusiveBlockLength constant scale
  have hlengthTop : Tendsto length atTop atTop := by
    simpa [length] using
      IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop hscale hconstant
  have hlengthPos : ∀ᶠ n : ℕ in atTop, 0 < length n :=
    hlengthTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsMogulskiiScale.eventually_pos hscale
  have hnormLengthPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (length n) :=
    (hlengthTop.eventually (eventually_gt_atTop 0)).mono fun n hn =>
      Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hroot : Real.sqrt constant = amplitude := by
    dsimp [constant]
    rw [Real.rpow_two, Real.sqrt_sq (le_of_lt hamplitude)]
  have hnormRatio : Tendsto
      (fun n => normalization (length n) / scale n) atTop (nhds amplitude) := by
    have h := IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div
      hscale hconstant
    simpa [length, normalization, hroot] using h
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hP htight hlengthTop hscalePos hnormLengthPos hnormRatio
  have hdiscrete :=
    eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
      ν scale length (Z := id) hlimit hscalePos hlengthPos hlower hupper
      lowerBound (by
        intro i hi
        simpa [lowerBound, C, radius, constant, Real.rpow_two] using hmass i hi)
  refine ⟨constant, hconstant, ?_⟩
  filter_upwards [hdiscrete] with n hn
  simpa [length, lowerBound, C, radius, constant] using hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

end
