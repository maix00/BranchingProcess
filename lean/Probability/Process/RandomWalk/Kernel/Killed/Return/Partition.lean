/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Combinatorics.BranchingWalk.Walk.Path.Block.Partition.Basic

/-!
# Equal-block path interpretation of interval return kernels

For a real additive walk, a return block is expressed as simultaneous outer
corridor constraints on an equal partition together with an inner endpoint
constraint.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A killed real walk run for `blocks * length` steps and restricted to an
inner endpoint interval is exactly the equal-block outer-corridor event with
that endpoint constraint. -/
theorem returnKernel_Icc_apply_univ_mul_eq_blockCorridors_endsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {outerLower outerUpper returnLower returnUpper initial : ℝ}
    (hinitialOuter : initial ∈ Set.Icc outerLower outerUpper)
    (hinitialReturn : initial ∈ Set.Icc returnLower returnUpper)
    {blocks length : ℕ} (hblocks : 0 < blocks) (hlength : 0 < length) :
    returnKernel ν
        (Set.Icc outerLower outerUpper) measurableSet_Icc
        (Set.Icc returnLower returnUpper) measurableSet_Icc
        (blocks * length)
        ⟨initial, hinitialReturn⟩ Set.univ =
      independentIncrementLaw ν {increment |
        (∀ j < blocks, ∀ k ≤ length,
          initial + partialSum (j * length + k) increment ∈
            Set.Icc outerLower outerUpper) ∧
        initial + partialSum (blocks * length) increment ∈
          Set.Icc returnLower returnUpper} := by
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  congr 1
  ext increment
  change (StaysIn (Set.Icc outerLower outerUpper) (blocks * length)
      initial increment ∧
    initial + partialSum (blocks * length) increment ∈
      Set.Icc returnLower returnUpper) ↔ _
  rw [staysIn_Icc_iff_inClosedInterval
    outerLower outerUpper (blocks * length) initial
    hinitialOuter increment]
  rw [inClosedInterval_mul_iff_forall_block
    hblocks hlength outerLower outerUpper initial increment]
  rfl

end ProbabilityTheory.RandomWalk
