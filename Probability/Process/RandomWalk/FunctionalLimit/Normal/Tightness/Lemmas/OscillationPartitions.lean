/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Probability.Distributions.Gaussian.Real
import Probability.Distributions.DomainOfAttraction.Basic
import Probability.Process.RandomWalk.FunctionalLimit.OscillationPartitions
import Probability.Process.RandomWalk.Path.Truncation.Normalized
import all Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness.Lemmas.Oscillation

/-!
# Internal oscillation-partition bound for normal-domain tightness

Gaussian-domain local block bounds feed into the general multiscale
oscillation-partition construction. Together with compact-range control this
is the path-tightness input for the exponent-two functional limit. This
specialization is used only by `Tightness/Basic` and is grouped here with its
proof-specific local oscillation bounds.
## Internal proof declarations

- `exists_eventually_oscillationPartitions_bound_of_gaussian`: for every
  $0<\eta<1$, there are positive gap and oscillation-tolerance sequences
  $g_m,\alpha_m$ with $\alpha_m\to0$ such that eventually the normalized
  step-path law assigns mass at most $\eta$ to paths that admit no
  $(g_m,\alpha_m)$ oscillation-partition sequence.

-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- A centered random walk in the Gaussian domain of attraction has an
eventual multiscale oscillation-partition bound. The local path estimates are
derived from Feller's tail condition and the normalized truncated-variance
profile, with no finite-second-moment assumption. -/
lemma exists_eventually_oscillationPartitions_bound_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  let coefficient : ℝ → ℝ := gaussianOscillationBlockCoefficient
  have hcoefficient : ∀ {ε : ℝ}, 0 < ε → 0 < coefficient ε := by
    intro ε hε
    exact gaussianOscillationBlockCoefficient_pos hε
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnormalization n hn
  apply ProbabilityTheory.RandomWalk.FunctionalLimit.exists_eventually_oscillationPartitions_bound_of_localEstimates
    hscale coefficient hcoefficient 0 (by norm_num)
  · intro ε endpointDelta blockFraction width hε hEndpoint hBlock hsmall hwidth hwidthLower hratio
    exact eventually_measure_not_hasDoubleExcursionBound_le_of_gaussian
      h hnormalization (by norm_num : 0 < (1 : ℝ)) hε hEndpoint hBlock.le
      width hwidth hwidthLower hratio
  · intro ε endpointDelta blockFraction width hε hEndpoint hBlock hsmall hwidth hwidthLower hratio
    exact eventually_measure_not_hasEndpointOscillationBound_le_of_gaussian
      h hnormalization (by norm_num : 0 < (1 : ℝ)) hε hEndpoint hBlock.le
      width hwidthLower hratio
  · exact hη
  · exact hηone

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end
