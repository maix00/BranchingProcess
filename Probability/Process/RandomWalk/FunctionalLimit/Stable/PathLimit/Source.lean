/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Centering
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness

/-!
# Stable random-walk functional limits under source centering conventions

The generic path-law theorem takes tightness and negligible block centers as
inputs. In the uncentered scalar domain-of-attraction convention, block
centers vanish identically. These corollaries combine that fact with the
proved J1 tightness criteria below, at, and above stable index one.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {α : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
  {normalization : ℕ → ℝ}

/-- The uncentered stable random walk converges in J1 below index one.
The scalar domain-of-attraction hypothesis uses zero centering; the remaining
tail and norming hypotheses supply the already established J1 tightness. -/
theorem tendsto_normalizedStepPathLaw_of_index_lt_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hnorm hα₀ hα₁ htail)

/-- The uncentered stable random walk converges in J1 at index one under the
source sine-centering convention. The scalar domain-of-attraction hypothesis
uses zero centering, and the sine-centering condition supplies J1 tightness. -/
theorem tendsto_normalizedStepPathLaw_of_index_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw 1 μ unitIntervalClock P)
    (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hnorm htail hcenter)

/-- The uncentered stable random walk converges in J1 above index one. The
zero-centered scalar domain-of-attraction hypothesis forces zero mean; its
tail regular variation supplies the first moment and the J1 tightness input. -/
theorem tendsto_normalizedStepPathLaw_of_index_gt_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have hint : Integrable (fun x : ℝ => x) ν :=
    integrable_id_of_twoSidedTail_regularlyVarying hα₁ htail
  have hmean := hDOA.integral_eq_zero_of_index_gt_one
    hlimit hnorm hα₁ hα₂
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
      hnorm hα₀ hα₁ hα₂ htail hint hmean)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
