/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Algebra.BigOperators.AdditivePath.Bounds

/-!
# Entrance lower bounds for killed random walks

Finite IID cylinder events give explicit lower bounds for reaching a target
before killing.  The geometric verification that a particular cylinder stays
inside a corridor is deliberately supplied as a hypothesis, so this bridge
can be reused with intervals and more general additive state spaces.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory.RandomWalk


variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
  [AddCommMonoid E] [MeasurableAdd₂ E]

/-- If forcing the first `length` IID increments into `incrementSet` keeps
the walk alive and places its endpoint in `target`, the corresponding product
mass lower-bounds the killed transition mass to `target`. -/
theorem pow_measure_le_killedIncrementKernel_pow_apply_of_forall_mem
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (target : Set E) (htarget : MeasurableSet target)
    (incrementSet : Set E) (hincrementSet : MeasurableSet incrementSet)
    (length : ℕ) (initial : E)
    (hpath : ∀ increment : ℕ → E,
      (∀ k < length, increment k ∈ incrementSet) →
        StaysIn allowed length initial increment ∧
          initial + AdditivePath.displacement length increment ∈ target) :
    (ν incrementSet) ^ length ≤
      (killedIncrementKernel ν allowed hallowed ^ length) initial target := by
  rw [killedIncrementKernel_pow_apply_eq_staysIn_endsIn
      ν allowed hallowed target htarget length initial,
    ← iidSequenceLaw_measure_forall_lt ν incrementSet hincrementSet length]
  exact measure_mono fun increment hincrement => hpath increment hincrement

/-- For a real-valued walk, forcing every increment into one open interval
gives a concrete entrance lower bound whenever the deterministic interval of
possible positions stays inside `allowed` and its final interval lies in
`target`. -/
theorem pow_measure_Ioo_le_killedIncrementKernel_pow_apply
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (allowed : Set ℝ) (hallowed : MeasurableSet allowed)
    (target : Set ℝ) (htarget : MeasurableSet target)
    (lower upper : ℝ) (length : ℕ) (initial : ℝ)
    (hallowedPath : ∀ k ≤ length,
      Set.Icc (initial + k • lower) (initial + k • upper) ⊆ allowed)
    (hendpoint : Set.Icc (initial + length • lower)
        (initial + length • upper) ⊆ target) :
    (ν (Set.Ioo lower upper)) ^ length ≤
      (killedIncrementKernel ν allowed hallowed ^ length) initial target := by
  apply pow_measure_le_killedIncrementKernel_pow_apply_of_forall_mem
    ν allowed hallowed target htarget (Set.Ioo lower upper)
      measurableSet_Ioo length initial
  intro increment hincrement
  have hincrementClosed : ∀ k < length,
      increment k ∈ Set.Icc lower upper := by
    intro k hk
    exact ⟨(hincrement k hk).1.le, (hincrement k hk).2.le⟩
  constructor
  · intro k
    have hk : k.val + 1 ≤ length := k.isLt
    have hsum := AdditivePath.displacement_mem_Icc_nsmul_of_forall_lt_of_le
      hincrementClosed hk
    apply hallowedPath (k.val + 1) hk
    constructor <;> linarith [hsum.1, hsum.2]
  · have hsum := AdditivePath.displacement_mem_Icc_nsmul_of_forall_lt hincrementClosed
    apply hendpoint
    constructor <;> linarith [hsum.1, hsum.2]

end ProbabilityTheory.RandomWalk
