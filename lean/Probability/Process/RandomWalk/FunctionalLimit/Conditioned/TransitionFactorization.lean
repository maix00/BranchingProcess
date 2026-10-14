/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Sequence.IID
public import Topology.Algebra.BigOperators.PartialSum

/-!
# Independent prefix and meander-transition suffix

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.finiteNonnegativeTransitionEvent`:
  the finite-block version of $D_{N,\Delta}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurableSet_finiteNonnegativeTransitionEvent`:
  that finite-block event is measurable.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_prefixWindow_and_shiftedTransition`:
  for an increment window $I$, the probability that the first $m$
  increments lie in $I$ and the next $N$ increments satisfy
  $D_{N,\Delta}$ equals $\nu(I)^m\mathbb P(D_{N,\Delta})$.

This is the independent fixed-prefix and conditioned-meander suffix
factorization in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Appendix A.2, proof of the meander transition
lemma used in Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The transition event on a finite increment block. -/
def finiteNonnegativeTransitionEvent (n : ℕ) (width : ℝ) :
    Set (Fin n → ℝ) :=
  {block | (∀ k : Fin n,
      0 ≤ Fin.partialSum block k.succ ∧
      Fin.partialSum block k.succ ≤ 5 / 6 * width) ∧
    Fin.partialSum block (Fin.last n) ∈
      Set.Icc (5 / 12 * width) (11 / 24 * width)}

/-- The finite transition event depends measurably on its increment block. -/
theorem measurableSet_finiteNonnegativeTransitionEvent
    (n : ℕ) (width : ℝ) :
    MeasurableSet (finiteNonnegativeTransitionEvent n width) := by
  have hgrid : MeasurableSet
      {block : Fin n → ℝ | ∀ k : Fin n,
        Fin.partialSum block k.succ ∈ Set.Icc 0 (5 / 6 * width)} := by
    rw [show {block : Fin n → ℝ | ∀ k : Fin n,
          Fin.partialSum block k.succ ∈ Set.Icc 0 (5 / 6 * width)} =
        ⋂ k : Fin n,
          {block : Fin n → ℝ |
            Fin.partialSum block k.succ ∈ Set.Icc 0 (5 / 6 * width)} by
      ext block
      simp]
    exact MeasurableSet.iInter fun k =>
      measurableSet_Icc.preimage (by fun_prop)
  have hend : MeasurableSet
      {block : Fin n → ℝ |
        Fin.partialSum block (Fin.last n) ∈
          Set.Icc (5 / 12 * width) (11 / 24 * width)} :=
    measurableSet_Icc.preimage (by fun_prop)
  convert hgrid.inter hend using 1
  ext block
  simp [finiteNonnegativeTransitionEvent, Set.mem_Icc]

/-- Restricting an increment sequence to a finite block identifies its
transition event with the corresponding shifted infinite sequence event. -/
theorem blockCoordinates_mem_finiteNonnegativeTransitionEvent_iff
    (start n : ℕ) (width : ℝ) (increment : ℕ → ℝ) :
    Combinatorics.Sequence.blockCoordinates start n increment ∈
        finiteNonnegativeTransitionEvent n width ↔
      (fun k => increment (start + k)) ∈
        nonnegativeTransitionEvent n width := by
  unfold finiteNonnegativeTransitionEvent nonnegativeTransitionEvent
  constructor
  · rintro ⟨hgrid, hend⟩
    constructor
    · intro k
      have hk := hgrid k
      rw [partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd] at hk
      exact hk
    · rw [partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd] at hend
      exact hend
  · rintro ⟨hgrid, hend⟩
    constructor
    · intro k
      rw [partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd]
      exact hgrid k
    · rw [partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd]
      exact hend

/-- Independence of a fixed bounded prefix and the subsequent transition
block, in the precise product form used in Wang Yiyang, Appendix A.2. -/
theorem measure_prefixWindow_and_shiftedTransition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (window : Set ℝ) (hwindow : MeasurableSet window)
    (m n : ℕ) (width : ℝ) :
    iidSequenceLaw ν
        {increment | (∀ k < m, increment k ∈ window) ∧
          (fun k => increment (m + k)) ∈
            nonnegativeTransitionEvent n width} =
      (ν window) ^ m *
        iidSequenceLaw ν (nonnegativeTransitionEvent n width) := by
  let prefixEvent : Set (Fin m → ℝ) :=
    {block | ∀ k : Fin m, block k ∈ window}
  let tailEvent : Set (Fin n → ℝ) :=
    finiteNonnegativeTransitionEvent n width
  have hprefix : MeasurableSet prefixEvent := by
    have heq : prefixEvent =
        ⋂ k : Fin m, {block : Fin m → ℝ | block k ∈ window} := by
      ext block
      simp [prefixEvent]
    rw [heq]
    exact MeasurableSet.iInter fun k : Fin m =>
      hwindow.preimage (measurable_pi_apply k)
  have htail : MeasurableSet tailEvent :=
    measurableSet_finiteNonnegativeTransitionEvent n width
  have hfactor := iidSequenceLaw_measure_inter_prefix_nextBlock ν m n
    prefixEvent tailEvent hprefix htail
  have hprefixEq :
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 m increment ∈ prefixEvent} =
      {increment | ∀ k < m, increment k ∈ window} := by
    ext increment
    simp [prefixEvent, Combinatorics.Sequence.blockCoordinates,
      Fin.forall_iff]
  have htailEq (start : ℕ) :
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates start n increment ∈ tailEvent} =
      {increment | (fun k => increment (start + k)) ∈
        nonnegativeTransitionEvent n width} := by
    ext increment
    exact blockCoordinates_mem_finiteNonnegativeTransitionEvent_iff
      start n width increment
  have hleftEq :
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 m increment ∈ prefixEvent ∧
        Combinatorics.Sequence.blockCoordinates m n increment ∈ tailEvent} =
      {increment | (∀ k < m, increment k ∈ window) ∧
        (fun k => increment (m + k)) ∈
          nonnegativeTransitionEvent n width} := by
    ext increment
    have hp := congrArg (fun s : Set (ℕ → ℝ) => increment ∈ s) hprefixEq
    have ht := congrArg (fun s : Set (ℕ → ℝ) => increment ∈ s) (htailEq m)
    simp only [Set.mem_ofPred_eq] at hp ht ⊢
    rw [hp, ht]
  rw [hleftEq, hprefixEq, htailEq 0] at hfactor
  have htailZero :
      {increment : ℕ → ℝ |
        (fun k => increment (0 + k)) ∈ nonnegativeTransitionEvent n width} =
      nonnegativeTransitionEvent n width := by
    ext increment
    simp
  rw [htailZero, iidSequenceLaw_measure_forall_lt ν window hwindow m] at hfactor
  exact hfactor

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
