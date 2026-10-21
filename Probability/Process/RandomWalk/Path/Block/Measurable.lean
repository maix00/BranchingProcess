/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Algebra.BigOperators.PartialSum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of increment blocks

The block operations are deterministic; this file records their measurability
when the increment sequence is regarded as the canonical sample space. It
also records measurability of the finite partial-sum map on a block.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


section FinitePartialSum

variable {E : Type*} [MeasurableSpace E] [AddMonoid E] [MeasurableAdd₂ E]

/-- The partial sum at a fixed time is measurable as a function of the finite
increment block. -/
theorem measurable_finPartialSum {length : ℕ}
    (time : Fin (length + 1)) :
    Measurable (fun increments : Fin length → E =>
      Fin.partialSum increments time) := by
  induction time using Fin.induction with
  | zero => exact measurable_const
  | succ time ih =>
    have hm := ih.add (measurable_pi_apply time)
    have heq : (fun increments : Fin length → E =>
        Fin.partialSum increments time.succ) =
      (fun increments : Fin length → E =>
        Fin.partialSum increments time.castSucc) +
        (fun increments : Fin length → E => increments time) := by
      funext increments
      simp only [Fin.partialSum_succ, Pi.add_apply]
    exact heq ▸ hm

end FinitePartialSum


/-- A large oscillation in one of finitely many equal blocks is a measurable
event on the infinite increment path space. -/
theorem measurableSet_exists_block_exists_abs_blockSum_ge
    (blocks length : ℕ) (threshold : ℝ) :
    MeasurableSet {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} := by
  rw [show {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} =
      ⋃ j ∈ Finset.range blocks, ⋃ k ∈ Finset.range (length + 1),
        {path | threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} by
    ext path
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    aesop]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const
        (continuous_abs.measurable.comp
          (blockSum_measurable (E := ℝ) (j * length) (k + 1)))

end ProbabilityTheory.RandomWalk
