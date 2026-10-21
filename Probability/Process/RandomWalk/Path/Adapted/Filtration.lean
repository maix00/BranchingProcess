/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Sequence.IID.Filtration
import Probability.Sequence.IID.Blocks.StoppingTime
public import Mathlib.Probability.Process.Adapted
import Probability.Sequence.IID.Blocks.Consecutive

/-!
# Adaptedness and block independence for random walks

The information available to a walk at time `n` is the generic prefix
filtration of its increment sequence. This file records the random-walk
consequences: a position is adapted, and a finite prefix is independent of a
later block sum under the canonical IID law.

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.indepFun_sequencePrefix_blockSum`: the
  increment prefix and a later block sum are independent under an IID law.
- `ProbabilityTheory.RandomWalk.positionProcess_adapted`: $S_n$ is measurable
  with respect to the first $n$ increments.
- `ProbabilityTheory.RandomWalk.displacement_measurable_prefix`: $S_k$ is
  measurable at prefix time $n$ whenever $k\le n$.
- `ProbabilityTheory.RandomWalk.displacement_natAdd_measurable_prefix`:
  a shifted block sum ending by $n$ is measurable at prefix time $n$.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [MeasurableSpace E]

section Block

variable [AddCommMonoid E] [MeasurableAdd₂ E]

/-- The complete increment prefix is independent of every following block
sum. Keeping the whole prefix is useful when conditioning on the walk's
available information rather than only on its current position. -/
theorem indepFun_sequencePrefix_blockSum
    (nu : Measure E) [IsProbabilityMeasure nu] (start length : ℕ) :
    IndepFun (Combinatorics.Sequence.blockCoordinates 0 (E := E) start)
      (AdditivePath.blockSum start length) (iidSequenceLaw nu) := by
  have hblocks := indepFun_blockCoordinates_blockCoordinates
    (E := E) nu 0 start length
  let sumBlock : (Fin length → E) → E := fun x ↦ ∑ k, x k
  have hsum : Measurable sumBlock := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ ↦ measurable_pi_apply k)
  have h := hblocks.comp measurable_id hsum
  have hleft : id ∘ Combinatorics.Sequence.blockCoordinates (E := E) 0 start =
      Combinatorics.Sequence.blockCoordinates 0 start := by
    funext increment k
    simp [Combinatorics.Sequence.blockCoordinates]
  have hright : sumBlock ∘ Combinatorics.Sequence.blockCoordinates
      (E := E) start length = AdditivePath.blockSum start length := by
    funext increment
    change (∑ k : Fin length, increment (start + (k : ℕ))) =
      AdditivePath.blockSum start length increment
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    exact Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ increment (start + k)) length
  simpa only [zero_add, hleft, hright] using h

end Block

section AddCommMonoid

variable [AddCommMonoid E] [MeasurableAdd₂ E]

/-- The position at time `n` is measurable with respect to the first `n`
increments. -/
theorem positionProcess_adapted (initial : E) :
    Adapted (sequencePrefixFiltration (E := E))
      (positionProcess initial) := by
  intro n
  rw [show positionProcess initial n = fun increment : ℕ → E ↦
      initial + ∑ k : Fin n, increment k by
    funext increment
    simp only [positionProcess, AdditivePath.fromIncrements,
      AdditivePath.displacement]
    rw [Fin.sum_univ_eq_sum_range]]
  exact measurable_const.add
    (Finset.measurable_sum Finset.univ
      fun k _ ↦ sequenceCoordinate_measurable n k)

/-- The displacement at any earlier time is measurable with respect to the
current increment-prefix sigma algebra. -/
theorem displacement_measurable_prefix {k n : ℕ} (hkn : k ≤ n) :
    Measurable[sequencePrefixFiltration (E := E) n]
      (AdditivePath.displacement (E := E) k) := by
  unfold AdditivePath.displacement
  exact Finset.measurable_sum (Finset.range k) fun i hi =>
    sequenceCoordinate_measurable n
      ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hkn⟩

/-- A block sum is measurable from any increment prefix containing the
whole block. -/
theorem displacement_natAdd_measurable_prefix
    (start length horizon : ℕ) (hbound : start + length ≤ horizon) :
    Measurable[sequencePrefixFiltration (E := E) horizon]
      (fun increment : ℕ → E =>
        AdditivePath.displacement length
          (fun k => increment (start + k))) := by
  unfold AdditivePath.displacement
  exact Finset.measurable_sum (Finset.range length) fun i hi =>
    sequenceCoordinate_measurable horizon
      ⟨start + i, by
        have hi' := Finset.mem_range.mp hi
        omega⟩

end AddCommMonoid

end ProbabilityTheory.RandomWalk

end
