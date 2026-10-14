/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Bessel.Support
public import Probability.Process.Brownian.Meander.Imhof

/-!
# Positive corridor mass under the Imhof measure

The public theorem in this file is:

- `BrownianMeander.imhofTilt_corridor_pos_of_brownian`: for a real Brownian
  process $B$ and $0<\rho<1/48$, the Imhof tilt of the radial law of three
  independent copies of $B$ assigns positive mass to
  $\mathcal U_{\sigma,\rho}$ when $\sigma>0$.

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
