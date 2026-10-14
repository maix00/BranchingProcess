/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Bessel.Support
public import Probability.Process.Brownian.Bessel.Endpoint
public import Probability.Process.Brownian.Meander.Imhof

/-!
# Positive corridor mass under the Imhof measure

The public theorems in this file are:

- `BrownianMeander.imhofTilt_corridor_pos_of_brownian`: a Brownian process
  with measurable time coordinates gives positive Imhof mass to the
  corridor $\mathcal U_{\sigma,\rho}$ for $\sigma>0$ and
  $0<\rho<1/48$.
- `BrownianMeander.imhofTilt_besselLaw_equivalent`: the Imhof tilt and
  the radial law of three independent copies of its continuous version
  have the same null sets.
- `BrownianMeander.imhofTilt_support_eq_besselLaw_support`: the two
  path laws have equal topological support.
- `BrownianMeander.imhofTilt_inverseDensity`: weighting the Imhof tilt
  by the reciprocal endpoint density recovers the radial Brownian law.
- `BrownianMeander.linearPath_mem_imhofTilt_support`: every nonnegative
  straight path belongs to the support of the Imhof transform of the
  radial law of three independent Brownian paths.

These results complete the support step in Wang Yiyang, *Asymptotic speed
of the $N$-branching random walk with infinite offspring*, Chapter 3,
Lemma 3.5, Appendix A.2, using the density from Jean-Pierre Imhof,
*Density factorizations for Brownian motion, meander and the
three-dimensional Bessel process, and applications*, Theorem 1.
The required continuous path version is constructed from the process's
measurable coordinates and almost-sure continuity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianMeander

private theorem continuousVersion_data
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]
    (hBrownian : IsBrownianReal B P) (hmeasurable : ∀ t, Measurable (B t)) :
    let Bc := hBrownian.continuousModification hmeasurable
    IsBrownianReal Bc P ∧ (∀ ω, Continuous (Bc · ω)) ∧
      (∀ t, Measurable (Bc t)) := by
  let Bc := hBrownian.continuousModification hmeasurable
  exact ⟨hBrownian.isBrownianReal_continuousModification hmeasurable,
    hBrownian.continuous_continuousModification hmeasurable,
    hBrownian.measurable_continuousModification hmeasurable⟩

/-- The Imhof density is strictly positive almost surely under the
three-dimensional Bessel path law. Consequently, the tilted and base laws
have the same null sets. -/
theorem imhofTilt_besselLaw_equivalent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable) ≪
        BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable ∧
      BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable ≪
        imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable) := by
  let Bc := hBrownian.continuousModification hmeasurable
  obtain ⟨hBc, hcont, hcoord⟩ := continuousVersion_data hBrownian hmeasurable
  let μ := BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable
  have hpositive : ∀ᵐ path ∂μ, imhofWeight path ≠ 0 := by
    filter_upwards [BrownianBessel3.ae_pos_endpoint_pathLaw
      hBc hcont hcoord] with path hpath
    exact ne_of_gt (imhofWeight_pos_of_endpoint_pos hpath)
  exact ⟨withDensity_absolutelyContinuous μ imhofWeight,
    withDensity_absolutelyContinuous' measurable_imhofWeight.aemeasurable
      hpositive⟩

/-- A strictly positive Imhof density preserves the Bessel path-law
support. -/
theorem imhofTilt_support_eq_besselLaw_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    (imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable)).support =
      (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable).support := by
  obtain ⟨hforward, hbackward⟩ :=
    imhofTilt_besselLaw_equivalent hBrownian hmeasurable
  exact Set.Subset.antisymm hforward.support_mono hbackward.support_mono

/-- Every nonnegative straight path belongs to the support of the Imhof
transform of the radial Brownian path law. This packages the BES(3) support
argument and invariance of support under a strictly positive density. -/
theorem linearPath_mem_imhofTilt_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 ≤ a) :
    Skorokhod.linearPath a ∈
      (imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable)).support := by
  rw [imhofTilt_support_eq_besselLaw_support hBrownian hmeasurable]
  exact BrownianBessel3.linearPath_mem_support
    (hBrownian.isBrownianReal_continuousModification hmeasurable)
    (hBrownian.continuous_continuousModification hmeasurable)
    (fun t => hBrownian.measurable_continuousModification hmeasurable t) ha

/-- The reciprocal Imhof density recovers the radial Brownian law. -/
theorem imhofTilt_inverseDensity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    (imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable)).withDensity
        (fun path => (imhofWeight path)⁻¹) =
      BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable := by
  let Bc := hBrownian.continuousModification hmeasurable
  obtain ⟨hBc, hcont, hcoord⟩ := continuousVersion_data hBrownian hmeasurable
  have hpositive : ∀ᵐ path ∂BrownianBessel3.pathLawOfBrownian
      hBrownian hmeasurable, imhofWeight path ≠ 0 := by
    filter_upwards [BrownianBessel3.ae_pos_endpoint_pathLaw
      hBc hcont hcoord] with path hpath
    exact ne_of_gt (imhofWeight_pos_of_endpoint_pos hpath)
  exact withDensity_inv_same measurable_imhofWeight hpositive
    (Filter.Eventually.of_forall fun path => ENNReal.ofReal_ne_top)

/-- The Imhof transform of the radial law of three independent Brownian
paths gives positive mass to the open corridor used by Wang Yiyang. -/
theorem imhofTilt_corridor_pos_of_brownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48) :
    0 < imhofTilt (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable)
      (openCorridor sigma rho) := by
  let Bc := hBrownian.continuousModification hmeasurable
  obtain ⟨hBc, hcont, hcoord⟩ := continuousVersion_data hBrownian hmeasurable
  have hnonneg : 0 ≤ (7 / 16 : ℝ) / sigma :=
    (div_pos (by norm_num) hsigma).le
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable).support := by
    change Skorokhod.linearPath ((7 / 16) / sigma) ∈
      (BrownianBessel3.pathLawOfBrownian hBrownian hmeasurable).support
    exact BrownianBessel3.linearPath_mem_support
      hBc hcont hcoord hnonneg
  exact measure_openCorridor_pos_imhofTilt
    hsigma hrho hrhoSmall hsupport

end BrownianMeander

end
