/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event
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
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.blockCoordinates_mem_finiteNonnegativeTransitionEvent_iff`:
  a finite increment block satisfies this event exactly when the shifted
  infinite increment path satisfies $D_{N,\Delta}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurableSet_nonnegativeTransitionEvent`:
  the infinite-sequence realization of $D_{N,\Delta}$ is measurable.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurableSet_prefixWindow_and_shiftedTransition`:
  the fixed-prefix and shifted-transition intersection is measurable.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_prefixWindow_and_shiftedTransition`:
  for an increment window $I$, the probability that the first $m$
  increments lie in $I$ and the next $N$ increments satisfy
  $D_{N,\Delta}$ equals $\nu(I)^m\mathbb P(D_{N,\Delta})$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_reflectedPrefixWindow_and_shiftedTransition`:
  the same product identity for reflected increments with law
  $\nu\circ(x\mapsto-x)^{-1}$.

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

/-- The transition event on canonical infinite increment sequences is
measurable because it depends on one finite block. -/
theorem measurableSet_nonnegativeTransitionEvent
    (n : ℕ) (width : ℝ) :
    MeasurableSet (nonnegativeTransitionEvent n width) := by
  have hpre := (measurableSet_finiteNonnegativeTransitionEvent n width).preimage
    (measurable_blockCoordinates 0 n)
  convert hpre using 1
  ext increment
  simpa using
    (blockCoordinates_mem_finiteNonnegativeTransitionEvent_iff
      0 n width increment).symm

/-- The prefix-window and shifted-transition event is measurable. -/
theorem measurableSet_prefixWindow_and_shiftedTransition
    (window : Set ℝ) (hwindow : MeasurableSet window)
    (m n : ℕ) (width : ℝ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        (∀ k < m, increment k ∈ window) ∧
        (fun k => increment (m + k)) ∈
          nonnegativeTransitionEvent n width} := by
  have hprefix : MeasurableSet
      {increment : ℕ → ℝ | ∀ k < m, increment k ∈ window} := by
    have heq :
        {increment : ℕ → ℝ | ∀ k < m, increment k ∈ window} =
          ⋂ k : Fin m, {increment : ℕ → ℝ | increment k ∈ window} := by
      ext increment
      simp [Fin.forall_iff]
    rw [heq]
    exact MeasurableSet.iInter fun k : Fin m =>
      hwindow.preimage (measurable_pi_apply (k : ℕ))
  have htail : MeasurableSet
      {increment : ℕ → ℝ |
        (fun k => increment (m + k)) ∈ nonnegativeTransitionEvent n width} :=
    (measurableSet_nonnegativeTransitionEvent n width).preimage
      (measurable_natAdd m)
  exact hprefix.inter htail

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

/-- The reflected prefix and suffix have the product probability of the
corresponding events under the reflected increment law. -/
theorem measure_reflectedPrefixWindow_and_shiftedTransition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (window : Set ℝ) (hwindow : MeasurableSet window)
    (m n : ℕ) (width : ℝ) :
    iidSequenceLaw ν
        {increment | (∀ k < m, -increment k ∈ window) ∧
          (fun k => -increment (m + k)) ∈
            nonnegativeTransitionEvent n width} =
      ((ν.map fun x : ℝ => -x) window) ^ m *
        iidSequenceLaw (ν.map fun x : ℝ => -x)
          (nonnegativeTransitionEvent n width) := by
  let νreflected := ν.map fun x : ℝ => -x
  let reflect : (ℕ → ℝ) → (ℕ → ℝ) :=
    fun increment k => -increment k
  let event : Set (ℕ → ℝ) :=
    {increment | (∀ k < m, increment k ∈ window) ∧
      (fun k => increment (m + k)) ∈
        nonnegativeTransitionEvent n width}
  have hreflect : Measurable reflect :=
    Measurable.of_eval fun k => measurable_neg.comp (measurable_pi_apply k)
  have hevent : MeasurableSet event :=
    measurableSet_prefixWindow_and_shiftedTransition window hwindow m n width
  have hmap := iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => -x) measurable_neg
  have hpreimage : reflect ⁻¹' event =
      {increment : ℕ → ℝ |
        (∀ k < m, -increment k ∈ window) ∧
        (fun k => -increment (m + k)) ∈
          nonnegativeTransitionEvent n width} := by
    rfl
  calc
    iidSequenceLaw ν
        {increment | (∀ k < m, -increment k ∈ window) ∧
          (fun k => -increment (m + k)) ∈
            nonnegativeTransitionEvent n width} =
        (iidSequenceLaw ν).map reflect event := by
          rw [Measure.map_apply hreflect hevent, hpreimage]
    _ = iidSequenceLaw νreflected event := by rw [hmap]
    _ = (νreflected window) ^ m *
          iidSequenceLaw νreflected
            (nonnegativeTransitionEvent n width) :=
      measure_prefixWindow_and_shiftedTransition νreflected
        window hwindow m n width

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
