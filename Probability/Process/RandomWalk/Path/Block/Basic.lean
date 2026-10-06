/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Block
public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Sequence.Block

/-!
# Measurable increment blocks

The finite sums and coordinate maps are defined algebraically. This module
records their measurability on the increment-path sample space.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

theorem paddedBlockCoordinates_measurable {E : Type*}
    [MeasurableSpace E] (start length : ℕ) (default : E) :
    Measurable (fun increment : ℕ → E =>
      AdditivePath.paddedBlockCoordinates start length default increment) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < length
  · change Measurable (fun increment : ℕ → E =>
      if k < length then increment (start + k) else default)
    simp only [ite_eq_left hk]
    exact measurable_pi_apply (start + k)
  · change Measurable (fun increment : ℕ → E =>
      if k < length then increment (start + k) else default)
    simp only [ite_eq_right hk]
    exact measurable_const

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
