module

public import Combinatorics.BranchingWalk.Walk.Path.Block.Partition
public import Probability.BranchingRandomWalk.Walk.Kernel.Killed

/-!
# Equal-block representation of killed-walk survival

The remaining mass of a killed additive kernel over an equal-block time
partition is identified with the corresponding deterministic block-corridor
event under the canonical increment law.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Survival of the restricted closed-interval kernel over `blocks * length`
steps is exactly simultaneous closed-interval containment on every coordinate
of every block. -/
theorem killedIncrementKernelOn_Icc_remainingMass_mul_eq_blockCorridors
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (initial : Set.Icc lower upper)
    {blocks length : ℕ} (hblocks : 0 < blocks) (hlength : 0 < length) :
    Kernel.remainingMass
        (killedIncrementKernelOn ν (Set.Icc lower upper) measurableSet_Icc)
        (blocks * length) initial =
      independentIncrementLaw ν {increment | ∀ j < blocks, ∀ k ≤ length,
        (initial : ℝ) + partialSum (j * length + k) increment ∈
          Set.Icc lower upper} := by
  rw [killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw]
  unfold independentIncrementLaw
  congr 1
  ext increment
  simp only [Set.mem_ofPred_eq]
  rw [staysIn_Icc_iff_inClosedInterval lower upper _ initial initial.property,
    inClosedInterval_mul_iff_forall_block hblocks hlength]

/-- Ambient-state version of the equal-block survival identity.  The initial
position is assumed to lie in the closed interval so that time zero is part of
the block-corridor event. -/
theorem killedIncrementKernel_Icc_remainingMass_mul_eq_blockCorridors
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper initial : ℝ) (hinitial : initial ∈ Set.Icc lower upper)
    {blocks length : ℕ} (hblocks : 0 < blocks) (hlength : 0 < length) :
    Kernel.remainingMass
        (killedIncrementKernel ν (Set.Icc lower upper) measurableSet_Icc)
        (blocks * length) initial =
      independentIncrementLaw ν {increment | ∀ j < blocks, ∀ k ≤ length,
        initial + partialSum (j * length + k) increment ∈
          Set.Icc lower upper} := by
  unfold Kernel.remainingMass
  rw [killedIncrementKernel_Icc_pow_apply_univ
    ν lower upper (blocks * length) initial hinitial]
  congr 1
  ext increment
  simp only [Set.mem_ofPred_eq]
  exact inClosedInterval_mul_iff_forall_block
    hblocks hlength lower upper initial increment

end ProbabilityTheory.RandomWalk
