/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Probability.Process.RandomWalk.Path.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Oscillation bounds for real-valued paths

The oscillation bound is stated for an arbitrary index type.  It therefore
applies to finite walk segments as well as to continuous-time paths.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- A real-valued path has oscillation at most `bound` when any two of its
values differ by at most `bound`. -/
def OscillationBounded {Time : Type*} (path : Time → ℝ) (bound : ℝ) : Prop :=
  ∀ s t, |path s - path t| ≤ bound

/-- Increasing the allowed oscillation preserves boundedness. -/
theorem OscillationBounded.mono {Time : Type*} {path : Time → ℝ}
    {bound₁ bound₂ : ℝ} (hbound : bound₁ ≤ bound₂)
    (hpath : OscillationBounded path bound₁) :
    OscillationBounded path bound₂ :=
  fun s t => (hpath s t).trans hbound

/-- Oscillation boundedness is symmetric in its two path indices. -/
theorem OscillationBounded.symm {Time : Type*} {path : Time → ℝ}
    {bound : ℝ} (hpath : OscillationBounded path bound) (s t : Time) :
    |path t - path s| ≤ bound := by
  simpa [abs_sub_comm] using hpath s t

/-- The strict range-oscillation event for the partial-sum path through time
`n`. It is translation invariant: it constrains pairwise differences, not the
position of the path relative to a fixed center. -/
def partialSumRangeOscillationLTEvent (width : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {increment | ∀ i j : Fin (n + 1),
    |AdditivePath.displacement (i : ℕ) increment -
      AdditivePath.displacement (j : ℕ) increment| < width}

/-- The strict partial-sum range event is measurable. -/
theorem measurableSet_partialSumRangeOscillationLTEvent (width : ℝ) (n : ℕ) :
    MeasurableSet (partialSumRangeOscillationLTEvent width n) := by
  rw [show partialSumRangeOscillationLTEvent width n =
      ⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1),
        {increment : ℕ → ℝ |
          |AdditivePath.displacement (i : ℕ) increment -
            AdditivePath.displacement (j : ℕ) increment| < width} by
    ext increment
    simp [partialSumRangeOscillationLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    exact measurableSet_Iio.preimage <|
      continuous_abs.measurable.comp <|
        (displacement_measurable (i : ℕ)).sub
          (displacement_measurable (j : ℕ))

/-- Probability of the strict partial-sum range event under an
increment-path law. -/
def partialSumRangeOscillationLTProbability
    (incrementLaw : Measure (ℕ → ℝ)) (width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw (partialSumRangeOscillationLTEvent width n)

/-- A longer-horizon range event is contained in the corresponding shorter
one, since the latter observes only an initial segment of the partial-sum
path. -/
theorem partialSumRangeOscillationLTProbability_antitone_horizon
    (incrementLaw : Measure (ℕ → ℝ)) (width : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    partialSumRangeOscillationLTProbability incrementLaw width n ≤
      partialSumRangeOscillationLTProbability incrementLaw width m := by
  unfold partialSumRangeOscillationLTProbability partialSumRangeOscillationLTEvent
  apply measure_mono
  intro increment h i j
  exact h ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

end ProbabilityTheory.RandomWalk

end
