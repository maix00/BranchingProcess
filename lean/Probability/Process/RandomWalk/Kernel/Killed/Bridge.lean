/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Probability.Kernel.Survival.Bridge

/-! # Killed block paths with a terminal bridge -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- Uniform return-block lower bounds, followed by one uniform bridge bound,
give a lower bound for a killed walk that stays in `allowed` throughout the
exact total duration and ends in a possibly different target set. -/
theorem iidSequenceLaw_staysIn_endsIn_ge_of_returnSequenceExit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (allowed core target : Set ℝ)
    (hallowed : MeasurableSet allowed) (hcore : MeasurableSet core)
    (htarget : MeasurableSet target) (lengths : List ℕ) (exitLength : ℕ)
    (returnLower bridgeLower : ℝ≥0∞)
    (hreturn : ∀ length ∈ lengths, ∀ x : core,
      returnLower ≤ returnKernel ν allowed hallowed core hcore length x Set.univ)
    (hbridge : ∀ x : core,
      bridgeLower ≤ ProbabilityTheory.Kernel.bridgeKernel
        (killedIncrementKernel ν allowed hallowed) core target htarget exitLength
        x Set.univ) :
    ∀ x : core,
      returnLower ^ lengths.length * bridgeLower ≤
        iidSequenceLaw ν
          {increment | StaysIn allowed
              (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths + exitLength)
              (x : ℝ) increment ∧
            (x : ℝ) + AdditivePath.displacement
              (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths + exitLength)
              increment ∈ target} := by
  let K := killedIncrementKernel ν allowed hallowed
  have hblock : ∀ length ∈ lengths, ∀ x : core,
      returnLower ≤ ProbabilityTheory.Kernel.returnKernel K core hcore length x
        Set.univ := by
    intro length hmem x
    simpa [K, returnKernel] using hreturn length hmem x
  have hsequenceExit :=
    ProbabilityTheory.Kernel.mul_pow_le_returnKernelSequenceExit_apply_univ
      K core hcore lengths returnLower bridgeLower hblock target htarget exitLength
      hbridge
  have hambient := ProbabilityTheory.Kernel.returnKernelSequenceExit_apply_univ_le
    K core target hcore htarget lengths exitLength
  intro x
  rw [← killedIncrementKernel_pow_apply_eq_staysIn_endsIn
    ν allowed hallowed target htarget
    (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths + exitLength)
    (x : ℝ)]
  exact (hsequenceExit x).trans (hambient x)

end ProbabilityTheory.RandomWalk

end
