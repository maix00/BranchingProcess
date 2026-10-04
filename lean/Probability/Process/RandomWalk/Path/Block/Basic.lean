/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Block
public import Probability.Process.RandomWalk.Path.Basic

/-!
# Measurable increment blocks

The finite sums and coordinate maps are defined algebraically. This module
records their measurability on the increment-path sample space.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

theorem blockCoordinates_measurable {E : Type*} [MeasurableSpace E]
    (start length : ℕ) :
    Measurable (AdditivePath.blockCoordinates (E := E) start length) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (start + k)

theorem blockSum_measurable {E : Type*} [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E] (start length : ℕ) :
    Measurable (AdditivePath.blockSum (E := E) start length) := by
  change Measurable (fun increment : ℕ → E =>
    AdditivePath.blockSum start length increment)
  rw [show (fun increment : ℕ → E =>
      AdditivePath.blockSum start length increment) =
        fun increment =>
          AdditivePath.displacement length (fun k => increment (start + k)) by
    funext increment
    exact AdditivePath.blockSum_eq_displacement_natAdd start length increment]
  exact (displacement_measurable length).comp (measurable_natAdd start)

end ProbabilityTheory.RandomWalk

end
