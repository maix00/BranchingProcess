/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Window.Core
import Probability.Sequence.IID.Blocks.Consecutive

/-!
# Closed-interval restart factorization proof

This module contains the interval-specific IID block calculation used to
prove the public restarted-interval probability identity.

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.Restart.Lemmas.iidSequenceLaw_closedInterval_prefix_shift_mul`
  transfers independence of two finite coordinate blocks to closed-interval
  path events on the prefix and shifted tail.
-/

open MeasureTheory

section

namespace ProbabilityTheory.RandomWalk.Restart.Lemmas

/-- Under an IID increment law, closed-interval events on two consecutive
finite increment blocks have product probability. -/
lemma iidSequenceLaw_closedInterval_prefix_shift_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (cutoff tail : ℕ) :
    iidSequenceLaw ν {increment |
        InClosedInterval lower upper cutoff 0 increment ∧
          InClosedInterval lower upper tail 0
            (fun k => increment (cutoff + k))} =
      iidSequenceLaw ν {increment |
          InClosedInterval lower upper cutoff 0 increment} *
        iidSequenceLaw ν {increment |
          InClosedInterval lower upper tail 0 increment} := by
  let length : ℕ → ℕ := fun j => if j = 0 then cutoff else tail
  let blockEvent : ∀ j : Fin 2, Set (Fin (length j.val) → ℝ) :=
    fun _ => {increment | FiniteInClosedInterval lower upper 0 increment}
  have hfactor := iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length 2 blockEvent
    (fun j => measurableSet_finiteInClosedInterval lower upper 0 (length j.val))
  have hpathEvent :
      {increment : ℕ → ℝ | ∀ j : Fin 2,
        Combinatorics.Sequence.blockCoordinates
          (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
            blockEvent j} =
      {increment | InClosedInterval lower upper cutoff 0 increment ∧
        InClosedInterval lower upper tail 0
          (fun k => increment (cutoff + k))} := by
    ext increment
    constructor
    · intro h
      constructor
      · have hzero := h ⟨0, by omega⟩
        simpa [length, blockEvent] using
          (finiteInClosedInterval_blockCoordinates_iff
            lower upper 0 0 cutoff increment).mp hzero
      · have hone := h ⟨1, by omega⟩
        simpa [length, blockEvent, Combinatorics.Sequence.blockStart] using
          (finiteInClosedInterval_blockCoordinates_iff
            lower upper 0 cutoff tail increment).mp hone
    · rintro ⟨hprefix, htail⟩ j
      fin_cases j
      · have hprefix' : InClosedInterval lower upper cutoff 0
            (fun k => increment (0 + k)) := by
          simpa [Nat.zero_add] using hprefix
        exact (finiteInClosedInterval_blockCoordinates_iff
          lower upper 0 0 cutoff increment).mpr hprefix'
      · simpa [length, blockEvent, Combinatorics.Sequence.blockStart] using
          (finiteInClosedInterval_blockCoordinates_iff
            lower upper 0 cutoff tail increment).mpr htail
  rw [hpathEvent] at hfactor
  have hzeroBlock (n : ℕ) :
      iidSequenceLaw ν {increment : ℕ → ℝ |
        FiniteInClosedInterval lower upper 0
          (Combinatorics.Sequence.blockCoordinates 0 n increment)} =
        iidSequenceLaw ν {increment | InClosedInterval lower upper n 0 increment} := by
    congr 1
    ext increment
    simpa [Nat.zero_add] using
      (finiteInClosedInterval_blockCoordinates_iff
        lower upper 0 0 n increment)
  rw [Fin.prod_univ_succ, Fin.prod_univ_one] at hfactor
  simp [length, blockEvent] at hfactor
  rw [hzeroBlock cutoff, hzeroBlock tail] at hfactor
  exact hfactor

end ProbabilityTheory.RandomWalk.Restart.Lemmas

end
