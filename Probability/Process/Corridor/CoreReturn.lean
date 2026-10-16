/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Recurrence.BlockBounds
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing

/-!
# Finite-block corridor return recurrences

These power inductions concern only measurable process events and a
one-block probability recurrence. They do not assume a stable law; a process
specific proof supplies the recurrence separately.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Iterating a one-step lower bound for a rational prefix corridor with an
interior endpoint return gives the corresponding power bound. -/
theorem pow_le_measure_prefixCorridorReturn_of_steps
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ}
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper coreLower coreUpper : ℝ)
    (c : ENNReal)
    (hzero : 1 ≤ P (rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks 0))
    (hstep : ∀ j : Fin blocks,
      c * P (rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks j.val) ≤
        P (rationalUniformPrefixCorridorReturnEvent X
          lower upper coreLower coreUpper hblocks (j.val + 1))) :
    c ^ blocks ≤ P (rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks blocks) := by
  apply pow_le_measure_of_mul_le_succ P
    (fun m => rationalUniformPrefixCorridorReturnEvent X
      lower upper coreLower coreUpper hblocks m) blocks c
  · exact hzero
  · intro j hj
    exact hstep ⟨j, hj⟩

/-- Iterating a one-step lower bound for a rational prefix corridor gives the
corresponding power bound. -/
theorem pow_le_measure_prefixCorridor_of_steps
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ}
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper : ℝ) (c : ENNReal)
    (hzero : 1 ≤ P (rationalUniformPrefixCorridorEvent X
      lower upper hblocks 0))
    (hstep : ∀ j : Fin blocks,
      c * P (rationalUniformPrefixCorridorEvent X lower upper
          hblocks j.val) ≤
        P (rationalUniformPrefixCorridorEvent X lower upper
          hblocks (j.val + 1))) :
    c ^ blocks ≤
      P (rationalUniformPrefixCorridorEvent X lower upper hblocks blocks) := by
  apply pow_le_measure_of_mul_le_succ P
    (fun m => rationalUniformPrefixCorridorEvent X lower upper hblocks m)
    blocks c
  · exact hzero
  · intro j hj
    exact hstep ⟨j, hj⟩

end ProbabilityTheory

end
