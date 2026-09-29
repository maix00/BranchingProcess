module

public import Combinatorics.BranchingWalk.Walk.Path.Block.Basic

/-!
# Measurability of increment blocks

The block operations are deterministic; this file records their measurability
when the increment sequence is regarded as the canonical sample space.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A large oscillation in one of finitely many equal blocks is a measurable
event on the infinite increment path space. -/
theorem measurableSet_exists_block_exists_abs_blockSum_ge
    (blocks length : ℕ) (threshold : ℝ) :
    MeasurableSet {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} := by
  rw [show {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} =
      ⋃ j ∈ Finset.range blocks, ⋃ k ∈ Finset.range (length + 1),
        {path | threshold ≤ |blockSum (j * length) (k + 1) path|} by
    ext path
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    aesop]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const
        (continuous_abs.measurable.comp
          (blockSum_measurable (E := ℝ) (j * length) (k + 1)))

end ProbabilityTheory.RandomWalk
