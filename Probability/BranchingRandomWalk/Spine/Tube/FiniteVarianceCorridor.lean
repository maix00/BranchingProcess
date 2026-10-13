/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.IncrementProcess
import Probability.BranchingRandomWalk.Spine.Tube.MRCAExpansion
import Probability.Process.RandomWalk.SmallDeviation.Entrance.FiniteVarianceEndpointCorridor

/-!
# Finite variance spine corridors

The entrance and stable endpoint bridge probability is rewritten as the
affine corridor event used by the branching random walk path count.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The fixed-window event from the finite-variance random-walk corridor
estimate is exactly the affine path corridor used in the spine pair expansion. -/
theorem endpointCorridorEvent_eq_affineCorridorThrough
    (n : ℕ) (D ratio : ℝ) :
    {increment : ℕ → ℝ |
      InClosedInterval (-ratio * D) 0 n 0 increment ∧
        AdditivePath.displacement n increment ∈
          Set.Icc (-ratio * D) ((-ratio + 1) * D)} =
    {increment : ℕ → ℝ |
      RandomWalk.history n 0 increment ∈
        affineCorridorThrough n (-ratio * D) 0 (ratio * D)
          ((-ratio + 1) * D)} := by
  ext increment
  simp only [Set.mem_setOf_eq, InClosedInterval, InWindows,
    affineCorridorThrough]
  have hwidth : -ratio * D + ratio * D = 0 := by ring
  have hlast : RandomWalk.history n 0 increment
      ⟨n, Nat.lt_succ_self n⟩ = AdditivePath.displacement n increment := by
    simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
  constructor
  · rintro ⟨hpath, hend⟩
    constructor
    · intro k
      rcases Set.mem_Icc.mp (hpath k) with ⟨hlo, hhi⟩
      constructor
      · simpa only [zero_mul, add_zero] using hlo
      · simpa only [zero_mul, add_zero, hwidth] using hhi
    · simpa only [hlast] using hend.2
  · rintro ⟨hpath, hend⟩
    constructor
    · intro k
      rcases hpath k with ⟨hlo, hhi⟩
      have hupper : history n 0 increment k ≤ 0 := by
        simpa only [zero_mul, add_zero, hwidth] using hhi
      exact Set.mem_Icc.mpr
        ⟨by simpa only [zero_mul, add_zero] using hlo, hupper⟩
    · have hlastPath := hpath ⟨n, Nat.lt_succ_self n⟩
      have hlower : -ratio * D ≤ AdditivePath.displacement n increment := by
        calc
          -ratio * D = -ratio * D + 0 * (n : ℝ) := by ring
          _ ≤ history n 0 increment ⟨n, Nat.lt_succ_self n⟩ := hlastPath.1
          _ = AdditivePath.displacement n increment := hlast
      have hupper : AdditivePath.displacement n increment ≤ (-ratio + 1) * D := by
        calc
          AdditivePath.displacement n increment =
              history n 0 increment ⟨n, Nat.lt_succ_self n⟩ := hlast.symm
          _ ≤ (-ratio + 1) * D := hend
      exact ⟨hlower, hupper⟩

/-- Finite variance gives an explicit lower bound on the tilted-spine
probability of the affine corridor. The lower bound is the entrance factor
times the stable cell-bridge factor, with every stable-process input derived
inside the random-walk theorem from the centered second moment. -/
theorem exists_eventually_tiltedIncrementFieldLaw_affineCorridor_lowerBound_of_centeredSecondMoment
    {ι : Type*} [Countable ι] {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw φ (-1) μ)
    {sigma : ℝ} (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) {scale : ℕ → ℝ}
    (hscale : RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale scale)
    (ratio : ℝ) (hratio : 1 < ratio) :
    ∃ C : ℝ, C < 0 ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ENNReal.ofReal (Real.exp
          ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) *
            amplitude ^ (2 : ℝ))) ^
            (Asymptotics.balancedBlockCount
              (finiteVarianceBridgeLength scale n -
                stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1) *
            (q / (finiteVarianceEntranceLength scale n : ℝ≥0∞)) ≤
          tiltedIncrementFieldLaw φ μ
            {increment : ℕ → ℝ |
              RandomWalk.history n 0 increment ∈
                affineCorridorThrough n (-ratio * scale n) 0
                  (ratio * scale n) ((-ratio + 1) * scale n)} := by
  obtain ⟨C, hC, q, hq, amplitude, hamplitude, n₀, hbound⟩ :=
    exists_eventually_iidSequenceLaw_endpointCorridor_lowerBound_of_centeredSecondMoment
      hνMoment hsigma hscale ratio hratio
  refine ⟨C, hC, q, hq, amplitude, hamplitude, n₀, ?_⟩
  intro n hn
  have hevent := endpointCorridorEvent_eq_affineCorridorThrough n (scale n) ratio
  have hlaw : tiltedIncrementFieldLaw φ μ = iidSequenceLaw ν := by
    rw [hν]
    rfl
  have hbound' := hbound n hn
  rw [hevent, ← hlaw] at hbound'
  exact hbound'

end ProbabilityTheory.BranchingRandomWalk.Spine
