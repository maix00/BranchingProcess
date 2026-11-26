/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.ExpectedCumulativePopulation

/-!
# Logarithmic bound on expected cumulative population

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor.exists_eventually_lintegral_cumulativePopulation_le_log`:
  if the tilted law is centered with finite positive variance and $b>0$,
  the expected cumulative count with $w=b\log n$ is at most $C\log n$
  for some $C>0$ and all sufficiently large $n$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk

/-- Equation (3.13) of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 3,
Lemma 3.8. The sum indexed by n + 1 counts all positive generations. -/
theorem exists_eventually_lintegral_cumulativePopulation_le_log
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {sigma b : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, ∑' j : ℕ, pathGeneration φ (j + 1)
        ((affineCorridorPrefix (j + 1) (-(b * Real.log (n : ℝ))) 0
          (b * Real.log (n : ℝ))).indicator (fun _ => (1 : ℝ≥0∞))) 0 ω
        ∂offspringFieldLaw μ) ≤ ENNReal.ofReal (C * Real.log (n : ℝ)) := by
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  obtain ⟨C, hC, hExit⟩ := exists_lintegral_upperBoundaryExitTime_le_linear ν hcentered hsigma
  have hwidth : Tendsto (fun n : ℕ => b * Real.log (n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hb
  refine ⟨C * b, mul_pos hC hb, ?_⟩
  filter_upwards [hwidth.eventually_ge_atTop 1] with n hn
  let w := b * Real.log (n : ℝ)
  have h := lintegral_cumulativePopulation_le_meanExitTime φ μ hboundary
    (show 0 ≤ w from zero_le_one.trans hn)
  refine h.trans ?_
  change (∫⁻ z, (upperBoundaryExitTime w z : ℝ≥0∞) ∂iidSequenceLaw ν) ≤ _
  rw [mul_assoc]
  exact hExit w hn

end ProbabilityTheory.BranchingRandomWalk.Spine.LogarithmicCorridor

end
