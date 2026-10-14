/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window

/-!
# Finite path windows with a terminal interval

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FiniteInClosedIntervalEndsIn`:
  a path started at $y$ stays in $[l,u]$ through $n$ steps and ends in
  $[a,b]$.
- `ProbabilityTheory.RandomWalk.measurableSet_finiteInClosedIntervalEndsIn`:
  this finite-increment-vector event is measurable.
- `ProbabilityTheory.RandomWalk.finiteInClosedIntervalEndsIn_blockCoordinates_iff`:
  applying the event to a coordinate block equals the corresponding
  infinite-sequence corridor and endpoint event.

The endpoint-window event is the reusable finite-path version of the
horizontal sub-tubes in Wang Yiyang, *Asymptotic speed of the $N$-branching
random walk with infinite offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

/-- A finite sequence of increments stays in a fixed interval, including
time zero, and ends in a prescribed terminal interval. -/
def FiniteInClosedIntervalEndsIn
    (lower upper endLower endUpper initial : ℝ) {n : ℕ}
    (increment : Fin n → ℝ) : Prop :=
  FiniteInClosedInterval lower upper initial increment ∧
    initial + ∑ j : Fin n, increment j ∈ Set.Icc endLower endUpper

/-- The finite tube and terminal-window event is measurable. -/
theorem measurableSet_finiteInClosedIntervalEndsIn
    (lower upper endLower endUpper initial : ℝ) (n : ℕ) :
    MeasurableSet
      {increment : Fin n → ℝ |
        FiniteInClosedIntervalEndsIn lower upper endLower endUpper
          initial increment} := by
  exact (measurableSet_finiteInClosedInterval lower upper initial n).inter
    (measurableSet_Icc.preimage
      (measurable_const.add (Finset.measurable_sum Finset.univ
        fun j _ => measurable_pi_apply j)))

/-- Coordinate restriction preserves both the full path constraint and
the terminal constraint of a finite tube event. -/
theorem finiteInClosedIntervalEndsIn_blockCoordinates_iff
    (lower upper endLower endUpper initial : ℝ)
    (start n : ℕ) (increment : ℕ → ℝ) :
    FiniteInClosedIntervalEndsIn lower upper endLower endUpper initial
      (Combinatorics.Sequence.blockCoordinates start n increment) ↔
      InClosedInterval lower upper n initial
        (fun k => increment (start + k)) ∧
      initial + AdditivePath.displacement n
        (fun k => increment (start + k)) ∈ Set.Icc endLower endUpper := by
  have hsum :
      (∑ j : Fin n,
        Combinatorics.Sequence.blockCoordinates start n increment j) =
        AdditivePath.displacement n (fun k => increment (start + k)) := by
    rw [Finset.sum_fin_eq_sum_range]
    simp only [AdditivePath.displacement,
      Combinatorics.Sequence.blockCoordinates]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨(finiteInClosedInterval_blockCoordinates_iff
      lower upper initial start n increment).mp hpath, ?_⟩
    simpa only [hsum] using hend
  · rintro ⟨hpath, hend⟩
    refine ⟨(finiteInClosedInterval_blockCoordinates_iff
      lower upper initial start n increment).mpr hpath, ?_⟩
    simpa only [hsum] using hend

end ProbabilityTheory.RandomWalk

end
