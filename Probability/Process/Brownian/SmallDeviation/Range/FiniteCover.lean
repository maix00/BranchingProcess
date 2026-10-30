/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Path.Scaling.UnitInterval
public import Topology.ContinuousMap.Oscillation

import Probability.Process.RandomWalk.Path.Interpolation.Core
import Probability.Process.RandomWalk.Rademacher.Basic
import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Range.Corridor.Survival
import all Probability.Process.Brownian.SmallDeviation.Range.Lemmas.FiniteCoverTransfer

/-!
# Brownian range bound from a fixed spectral corridor cover

## Public declarations

- `ProbabilityTheory.Process.Brownian.SmallDeviation.Range.brownianRangeOscillation_le_fixedSpectralCover`:
  for $w>0$ and $m>0$, the probability that a Brownian path has range
  diameter at most $w$ is bounded by the sum of $m$ full-spectrum corridor
  estimates, each with exponent $-\pi^2/(2(w+3w/m)^2)$. The proof combines
  the fixed-corridor Donsker transfer with the finite-interval Rademacher
  survival estimate and its diffusive spectral limit. Its calculation lemmas
  are in `Lemmas/FiniteCoverTransfer.lean`.

The convergence input is the continuous-path Donsker theorem formalized as
`ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_brownian`,
corresponding to Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.Process.Brownian.SmallDeviation.Range

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

/-- Brownian range-oscillation probability is bounded by the complete
spectral correction summed over a fixed finite cover of possible minima.
The number of terms is fixed before taking the Donsker limit. -/
theorem brownianRangeOscillation_le_fixedSpectralCover
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (ContinuousMap.rangeOscillationSet width) ≤
      ∑ _j : Fin count, ENNReal.ofReal (4 *
        (Real.exp (-(Real.pi ^ 2) /
            (2 * (width + 3 * (width / count)) ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) /
            (2 * (width + 3 * (width / count)) ^ 2))))) := by
  have hcover := brownianRangeOscillation_le_sum_liminf_fixedCorridors
    hB hcontinuous hmeasurable hwidth hcount
  calc
    P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (ContinuousMap.rangeOscillationSet width) ≤
      ∑ j : Fin count, atTop.liminf (fun n =>
        normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j))) := hcover
    _ ≤ ∑ j : Fin count, ENNReal.ofReal (4 *
        (Real.exp (-(Real.pi ^ 2) /
            (2 * (width + 3 * (width / count)) ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) /
            (2 * (width + 3 * (width / count)) ^ 2))))) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hleft := ContinuousMap.oscillationCoverLower_lt_zero
        width count j hwidth hcount
      have hright := ContinuousMap.zero_lt_oscillationCoverUpper
        width count j hwidth hcount
      have hinterval := liminf_normalizedRademacherPath_openCorridor_le
        hleft hright
      have hlength := ContinuousMap.oscillationCoverUpper_sub_lower
        width count j
      rw [hlength] at hinterval
      exact hinterval

end ProbabilityTheory.Process.Brownian.SmallDeviation.Range

end
