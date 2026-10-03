/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail
public import Probability.Distributions.Stable.Attraction.NormingRatios.RegularVariation

/-!
# Stable attraction and the symmetric cosine defect

The squared-modulus defect of an increment characteristic function is the
cosine defect of the symmetrized increment law. This bridge keeps the law
whose tail enters the inverse Tauberian theorem explicit.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- In a stable domain of attraction, the cosine defect of the symmetrized
increment law is regularly varying at zero with the stable index. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedCosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Asymptotics.IsRegularlyVaryingAtZero
      (fun u => cosineDefectIntegral (symmetrizedMeasure ν) u) α := by
  have hreg := h.isRegularlyVarying_normDefect_atZero hlimit
  refine ⟨?_, ?_⟩
  · filter_upwards [hreg.eventually_pos] with u hu
    simpa only [cosineDefectIntegral_symmetrizedMeasure] using hu
  · intro s hs
    have heq : (fun u : ℝ =>
        cosineDefectIntegral (symmetrizedMeasure ν) (s * u) /
          cosineDefectIntegral (symmetrizedMeasure ν) u) =ᶠ[𝓝[>] (0 : ℝ)]
        fun u => (1 - ‖charFun ν (s * u)‖ ^ 2) /
          (1 - ‖charFun ν u‖ ^ 2) := by
      filter_upwards [] with u
      rw [cosineDefectIntegral_symmetrizedMeasure,
        cosineDefectIntegral_symmetrizedMeasure]
    exact (hreg.ratio_tendsto hs).congr' heq.symm

end ProbabilityTheory

end
