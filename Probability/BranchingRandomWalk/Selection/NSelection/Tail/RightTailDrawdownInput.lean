/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailPopulationLowCount
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Scaling

/-!
# First-stage drawdown input from finite variance

This file supplies the quantitative drawdown sequence needed by the
first-stage corridor pair estimate. The rate is the uniform Aïdékon--Hu
bound, with the short-prefix terms bounded by one.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The finite-variance upper bound for a drawdown window of width `width`.
Short prefixes use the probability bound one; longer prefixes use the
Aïdékon--Hu exponential estimate. -/
noncomputable def rightTailPositiveADrawdownPowerBound
    (width sigma target p : ℝ) (n : ℕ) : ℝ≥0∞ :=
  if width ^ (2 + p) ≤ (n : ℝ) then
    ENNReal.ofReal (Real.exp
      (-target * sigma ^ 2 * (n : ℝ) / width ^ 2))
  else 1

/-- Centered finite variance and a pre-Brownian realization produce a
finite-valued sequence `q` bounding every drawdown event
`noLargeDropEndpointBelowEvent n width width`. This is the exact random-walk
input consumed by the affine-corridor pair estimate when its drift is zero. -/
theorem exists_rightTailPositiveADrawdownPowerBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (target blockTarget p : ℝ)
    (htarget : 0 < target) (hblockTarget : target < blockTarget)
    (hblockTargetUpper : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ width : ℝ, delta0 ≤ width →
      ∀ n : ℕ,
        (iidSequenceLaw ν)
          (noLargeDropEndpointBelowEvent n width width) ≤
            rightTailPositiveADrawdownPowerBound width sigma target p n ∧
        rightTailPositiveADrawdownPowerBound width sigma target p n ≠ ∞ := by
  obtain ⟨delta0, hdelta0, hAH⟩ :=
    exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
      ν hν hsigma hB hcontinuous hmeasurable 1 target blockTarget p
      (by norm_num) htarget hblockTarget hblockTargetUpper hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro width hwidth n
  by_cases hlong : width ^ (2 + p) ≤ (n : ℝ)
  · have hbound := hAH width hwidth n hlong
    have hendpoint : width / 1 = width := by ring
    rw [hendpoint] at hbound
    constructor
    · simpa [rightTailPositiveADrawdownPowerBound, hlong] using hbound
    · simp [rightTailPositiveADrawdownPowerBound, hlong,
        ENNReal.ofReal_ne_top]
  · have hprob : iidSequenceLaw ν
        (noLargeDropEndpointBelowEvent n width width) ≤ 1 := by
      calc
        _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    constructor
    · simpa [rightTailPositiveADrawdownPowerBound, hlong] using hprob
    · simp [rightTailPositiveADrawdownPowerBound, hlong]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
