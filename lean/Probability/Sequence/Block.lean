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

Finite coordinate extraction is measurable for the product sigma-algebra on
sequence space.
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

end ProbabilityTheory

end
