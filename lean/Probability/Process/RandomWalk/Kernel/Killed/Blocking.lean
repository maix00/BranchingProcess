/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Kernel.Survival.Blocking

/-!
# Blocking horizontal-tube probabilities

The state space of the killed kernel is the tube itself.  Consequently,
uniform one-block estimates quantify exactly over admissible positions and
the abstract sub-Markov blocking bounds apply without imposing conditions on
irrelevant starting points outside the tube.
-/

open MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- The ambient killed kernel has the same horizontal-tube interpretation.
The endpoint order is chosen to match scaled intervals produced by block
arguments. -/
theorem remainingMass_killedIncrementKernel_scaled_Icc_eq_horizontalTubeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (n : ℕ) :
    Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (width * (-a)) (width * (1 - a))) measurableSet_Icc)
        n 0 =
      horizontalTubeProbability (iidSequenceLaw ν)
        a width n := by
  change (killedIncrementKernel ν
      (Set.Icc (width * (-a)) (width * (1 - a))) measurableSet_Icc ^ n)
      0 univ = _
  rw [killedIncrementKernel_pow_apply_univ]
  unfold horizontalTubeProbability
  congr 1
  ext increment
  simp only [StaysIn, InHorizontalTube, zero_add, Set.mem_Icc]
  constructor <;> intro h k
  · simpa [mul_comm] using h k
  · simpa [mul_comm] using h k

/-- The remaining mass of the interval-valued killed kernel is the horizontal
tube probability from zero. -/
theorem remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (n : ℕ) :
    Kernel.remainingMass
        (killedIncrementKernelOn ν
          (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
        n ⟨0, by constructor <;> nlinarith⟩ =
      horizontalTubeProbability (iidSequenceLaw ν)
        a width n := by
  rw [killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw]
  unfold horizontalTubeProbability
  congr 1
  ext increment
  simp only [StaysIn, InHorizontalTube, zero_add, Set.mem_Icc]

/-- Uniform survival estimates for one block give two-sided bounds for every
horizontal-tube duration, including an incomplete final block. -/
theorem horizontalTubeProbability_bounds_of_block
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    {block : ℕ} (hblock : 0 < block) (n : ℕ)
    (lower upper : ENNReal)
    (hlower : ∀ x : Set.Icc (-a * width) ((1 - a) * width),
      lower ≤ Kernel.remainingMass
        (killedIncrementKernelOn ν
          (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
        block x)
    (hupper : ∀ x : Set.Icc (-a * width) ((1 - a) * width),
      Kernel.remainingMass
        (killedIncrementKernelOn ν
          (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
        block x ≤ upper) :
    lower ^ (n / block + 1) ≤
        horizontalTubeProbability (iidSequenceLaw ν) a width n ∧
      horizontalTubeProbability (iidSequenceLaw ν) a width n ≤
        upper ^ (n / block) := by
  rw [← remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
    ν a width ha0 ha1 hwidth n]
  exact Kernel.remainingMass_bounds_of_block
    (killedIncrementKernelOn ν
      (Set.Icc (-a * width) ((1 - a) * width)) measurableSet_Icc)
    hblock n ⟨0, by constructor <;> nlinarith⟩ lower upper hlower hupper

end ProbabilityTheory.RandomWalk
