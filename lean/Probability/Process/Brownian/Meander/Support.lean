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

- `BrownianMeander.imhofTilt_corridor_pos_of_brownian`: for a real Brownian
  process $B$ and $0<\rho<1/48$, the Imhof tilt of the radial law of three
  independent copies of $B$ assigns positive mass to
  $\mathcal U_{\sigma,\rho}$ when $\sigma>0$.
- `BrownianMeander.imhofTilt_besselLaw_equivalent`: the Imhof tilt and
  the law of the three-dimensional Brownian radius are mutually
  absolutely continuous.
- `BrownianMeander.imhofTilt_support_eq_besselLaw_support`: their
  topological supports coincide.

The theorem completes the support step in Wang Yiyang, *Asymptotic speed of
the $N$-branching random walk with infinite offspring*, Chapter 3,
Lemma 3.5, Appendix A.2, using the density from Imhof, *Density
factorizations for Brownian motion, meander and the three-dimensional Bessel
process, and applications*, Theorem 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianMeander

/-- The endpoint density is strictly positive almost surely under the
three-dimensional Bessel path law. Consequently, the tilted and base laws
have the same null sets. -/
theorem imhofTilt_besselLaw_equivalent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    imhofTilt (BrownianBessel3.pathLaw P B hcontinuous) ≪
        BrownianBessel3.pathLaw P B hcontinuous ∧
      BrownianBessel3.pathLaw P B hcontinuous ≪
        imhofTilt (BrownianBessel3.pathLaw P B hcontinuous) := by
  let μ := BrownianBessel3.pathLaw P B hcontinuous
  have hpositive : ∀ᵐ path ∂μ, imhofWeight path ≠ 0 := by
    filter_upwards [BrownianBessel3.ae_pos_endpoint_pathLaw
      hBrownian hcontinuous hmeasurable] with path hpath
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
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    (imhofTilt (BrownianBessel3.pathLaw P B hcontinuous)).support =
      (BrownianBessel3.pathLaw P B hcontinuous).support := by
  obtain ⟨hforward, hbackward⟩ :=
    imhofTilt_besselLaw_equivalent hBrownian hcontinuous hmeasurable
  exact Set.Subset.antisymm hforward.support_mono hbackward.support_mono

/-- The Imhof transform of the radial law of three independent Brownian
paths gives positive mass to the open corridor used in the thesis. -/
theorem imhofTilt_corridor_pos_of_brownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48) :
    0 < imhofTilt (BrownianBessel3.pathLaw P B hcontinuous)
      (openCorridor sigma rho) := by
  have hnonneg : 0 ≤ (7 / 16 : ℝ) / sigma :=
    (div_pos (by norm_num) hsigma).le
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (BrownianBessel3.pathLaw P B hcontinuous).support := by
    change Skorokhod.linearPath ((7 / 16) / sigma) ∈
      (BrownianBessel3.pathLaw P B hcontinuous).support
    exact BrownianBessel3.linearPath_mem_support
      hBrownian hcontinuous hmeasurable hnonneg
  exact measure_openCorridor_pos_imhofTilt
    hsigma hrho hrhoSmall hsupport

end BrownianMeander

end
