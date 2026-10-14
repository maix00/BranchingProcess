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
- `ProbabilityTheory.RandomWalk.measurableSet_pairFiniteInClosedIntervalEndsIn`:
  the same event remains measurable when its initial position is a
  measurable function of a preceding block.

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

/-- A finite corridor and terminal-window event is measurable when the
initial position is read from another measurable coordinate block. -/
theorem measurableSet_pairFiniteInClosedIntervalEndsIn
    {A : Type*} [MeasurableSpace A] {n : ℕ}
    (lower upper endLower endUpper : ℝ)
    (initial : A → ℝ) (hinitial : Measurable initial) :
    MeasurableSet
      {p : A × (Fin n → ℝ) |
        FiniteInClosedIntervalEndsIn
          lower upper endLower endUpper (initial p.1) p.2} := by
  have hinitialPair : Measurable (fun p : A × (Fin n → ℝ) => initial p.1) :=
    hinitial.comp measurable_fst
  have hpartial (k : Fin (n + 1)) :
      Measurable (fun p : A × (Fin n → ℝ) =>
        initial p.1 +
          ∑ j : Fin k, p.2
            ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩) := by
    exact hinitialPair.add (Finset.measurable_sum Finset.univ
      fun j _ => (measurable_pi_apply
        (⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ : Fin n)).comp
          measurable_snd)
  have hend : Measurable (fun p : A × (Fin n → ℝ) =>
      initial p.1 + ∑ j : Fin n, p.2 j) := by
    exact hinitialPair.add (Finset.measurable_sum Finset.univ
      fun j _ => (measurable_pi_apply j).comp measurable_snd)
  rw [show {p : A × (Fin n → ℝ) |
        FiniteInClosedIntervalEndsIn
          lower upper endLower endUpper (initial p.1) p.2} =
      (⋂ k : Fin (n + 1), {p | initial p.1 +
        ∑ j : Fin k, p.2
          ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ ∈
            Set.Icc lower upper}) ∩
      {p | initial p.1 + ∑ j : Fin n, p.2 j ∈
        Set.Icc endLower endUpper} by
    ext p
    simp [FiniteInClosedIntervalEndsIn, FiniteInClosedInterval]]
  exact (MeasurableSet.iInter fun k =>
    measurableSet_Icc.preimage (hpartial k)).inter
      (measurableSet_Icc.preimage hend)

end ProbabilityTheory.RandomWalk

end
