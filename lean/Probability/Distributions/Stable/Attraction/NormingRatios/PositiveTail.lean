/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian

/-!
# Right tails in a positive stable domain of attraction

The public theorem in this file is:

- `ProbabilityTheory.IsInDomainOfAttractionAlong.isRegularlyVarying_rightTail_of_nonneg`:
  if a probability law is supported on $[0,\infty)$ and is attracted to
  an $\alpha$-stable law with $0<\alpha<2$, then
  $x\mapsto\nu((x,\infty))$ is regularly varying with index $-\alpha$.

This is the one-sided tail consequence of stable attraction used for the
first descending ladder time in Francesco Caravenna and Loïc Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
Lemma 2.1, equation (2.3), DOI 10.1214/07-AIHP119.
-/

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory

/-- For a law supported on the nonnegative half-line, the regularly varying
two-sided tail in a stable domain of attraction is its right tail. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_rightTail_of_nonneg
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hneg : ν (Set.Iio 0) = 0) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun x : ℝ => ν.real (Set.Ioi x)) (-α) := by
  have hae : ∀ᵐ y ∂ν, 0 ≤ y := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using hneg
  have heq : (fun x : ℝ => ν.real {y : ℝ | x < |y|}) =
      (fun x : ℝ => ν.real (Set.Ioi x)) := by
    funext x
    change (ν {y : ℝ | x < |y|}).toReal = (ν (Set.Ioi x)).toReal
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hae] with y hy
    simp only [Set.mem_Ioi, abs_of_nonneg hy]
  rw [← heq]
  exact h.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂

end ProbabilityTheory

end
