/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Bessel.ThreeDimensional
public import Topology.Cadlag.Skorokhod.Path.Endpoint

/-!
# The endpoint of a three-dimensional Bessel path

The public theorems in this file are:

- `BrownianBessel3.ae_pos_endpoint`: for three independent Brownian
  coordinates, the radial path satisfies $R_1>0$ almost surely.
- `BrownianBessel3.ae_pos_endpoint_pathLaw`: the same conclusion under
  the pushed-forward Bessel path law.

This is the endpoint fact used with the density in Jean-Pierre Imhof,
*Density factorizations for Brownian motion, meander and the
three-dimensional Bessel process, and applications*, Journal of Applied
Probability 21 (1984), Theorem 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianBessel3

/-- The first coordinate of a three-dimensional Brownian sample is
nonzero at time one almost surely. -/
private lemma ae_first_coordinate_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P) :
    ∀ᵐ ω ∂productLaw P, B 1 ω.1 ≠ 0 := by
  have hsingle : ∀ᵐ ω ∂P, B 1 ω ≠ 0 := by
    exact (hBrownian.hasLaw_eval 1).ae_iff
      (measurableSet_setOfPred.1 (by
        convert (measurableSet_singleton (0 : ℝ)).compl using 1
        ext x
        simp)) |>.2
      (@Measure.ae_ne ℝ _ (gaussianReal 0 1)
        (nullSingletonClass_gaussianReal (by norm_num)) 0)
  change ∀ᵐ ω ∂P.prod (P.prod P), B 1 ω.1 ≠ 0
  exact (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P.prod P)).ae hsingle

/-- The radial endpoint of three independent Brownian coordinates is
strictly positive almost surely. -/
theorem ae_pos_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω)) :
    ∀ᵐ ω ∂productLaw P, 0 < path B hcontinuous ω ⊤ := by
  filter_upwards [ae_first_coordinate_ne_zero hBrownian] with ω hfirst
  change 0 < Real.sqrt ((B 1 ω.1) ^ 2 +
    (B 1 ω.2.1) ^ 2 + (B 1 ω.2.2) ^ 2)
  apply Real.sqrt_pos.2
  have hsq : 0 < (B 1 ω.1) ^ 2 := sq_pos_of_ne_zero hfirst
  nlinarith [sq_nonneg (B 1 ω.2.1), sq_nonneg (B 1 ω.2.2)]

/-- The Bessel path law concentrates on paths with a positive endpoint. -/
theorem ae_pos_endpoint_pathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ path ∂pathLaw P B hcontinuous, 0 < path ⊤ := by
  unfold pathLaw
  apply (ae_map_iff (measurable_path hcontinuous hmeasurable).aemeasurable
    (isOpen_lt continuous_const
      Skorokhod.continuous_apply_top).measurableSet).2
  exact ae_pos_endpoint hBrownian hcontinuous

end BrownianBessel3

end
