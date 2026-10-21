/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Sequence.Block
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of finite sequence blocks

The public declarations are:

- `ProbabilityTheory.measurable_blockCoordinates`: the coordinate map
  $f\mapsto(k\mapsto f(s+k))$ for $k<\ell$ is measurable.
- `ProbabilityTheory.paddedBlockCoordinates_measurable`: its extension by a
  fixed default value for $k\geq\ell$ is measurable.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The finite block map is measurable on sequence space. -/
theorem measurable_blockCoordinates (start length : ℕ) :
    Measurable (Combinatorics.Sequence.blockCoordinates (E := E) start length) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (start + k)

/-- The finite block map extended by a fixed value outside its index range is
measurable on sequence space. -/
theorem paddedBlockCoordinates_measurable {E : Type*} [MeasurableSpace E]
    (start length : ℕ) (default : E) :
    Measurable (fun sequence : ℕ → E =>
      Combinatorics.Sequence.paddedBlockCoordinates start length default sequence) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < length
  · change Measurable (fun sequence : ℕ → E =>
      if k < length then sequence (start + k) else default)
    simp only [ite_eq_left hk]
    exact measurable_pi_apply (start + k)
  · change Measurable (fun sequence : ℕ → E =>
      if k < length then sequence (start + k) else default)
    simp only [ite_eq_right hk]
    exact measurable_const

end ProbabilityTheory

end
