/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.ProcessExistence
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.CLT

/-!
# Gaussian path-law existence from random-walk tightness

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path.exists_gaussianStablePathLaw_with_escapeRate`:
  a centered unit-variance random walk yields a Gaussian unit-interval path
  law, a concatenated stable Lévy process, and the exponent-two escape rate
  $-\pi^2/8$.

The Gaussian unit-interval path law can be obtained as a subsequential limit
of the Rademacher walk. Its stable clock-law structure and the calibrated
escape rate then follow from the repo-owned path-law and stable-process
interfaces, without a separate Brownian-process witness.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open ProbabilityTheory.RandomWalk.FunctionalLimit.Normal
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

/-- The Gaussian unit-interval path law and its exponent-two escape rate can
be obtained from the Rademacher source by normal-domain tightness. The
concatenated unit-block process supplies the full-time stable-process
reference needed to calibrate the rate. -/
theorem exists_gaussianStablePathLaw_with_escapeRate
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    ∃ (P : ProbabilityMeasure (CadlagPath unitInterval ℝ))
      (Q : ProbabilityMeasure (ℕ → CadlagPath unitInterval ℝ))
      (X : ℝ≥0 → (ℕ → CadlagPath unitInterval ℝ) → ℝ),
      IsStableClockProcessLaw 2 (gaussianReal 0 (1 : ℝ≥0))
        UnitInterval.clock (P : Measure (CadlagPath unitInterval ℝ)) ∧
      IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) X
        (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) ∧
      HasStableProcessEscapeRate 2 (gaussianReal 0 1)
        (P : Measure (CadlagPath unitInterval ℝ)) (-(Real.pi ^ 2) / 8) := by
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  have hDOA : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0) := by
    simpa [normalization] using
      isInDomainOfAttractionAlong_gaussianReal_zero_one ν hν.1 hν.2
  have hnormalization : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (by norm_num)
  have htight :=
    isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian hDOA hnormalization
  obtain ⟨P, hP, _sub, _hsub, _hconv⟩ :=
    exists_stableClockProcessLaw_of_tightSource hDOA hstable htight
  let Q : Measure (ℕ → CadlagPath unitInterval ℝ) :=
    ProbabilityTheory.iidUnitPathBlockLaw (P : Measure (CadlagPath unitInterval ℝ))
  have hQ : IsProbabilityMeasure Q :=
    ProbabilityTheory.iidUnitPathBlockLaw_isProbabilityMeasure
      (P : Measure (CadlagPath unitInterval ℝ))
  let X : ℝ≥0 → (ℕ → CadlagPath unitInterval ℝ) → ℝ :=
    fun t ω => ProbabilityTheory.iidUnitPathBlockProcess ω t
  letI : IsProbabilityMeasure Q := hQ
  have hX : IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) X Q := by
    simpa [Q, X] using
      ProbabilityTheory.iidUnitPathBlockProcess_isStableLevyProcess hP
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  obtain ⟨C, hEscape⟩ :=
    hP.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  have hC :=
    ProbabilityTheory.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscape hX hscale
  refine ⟨P, ⟨Q, hQ⟩, X, hP, hX, ?_⟩
  simpa [hC] using hEscape

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

end
