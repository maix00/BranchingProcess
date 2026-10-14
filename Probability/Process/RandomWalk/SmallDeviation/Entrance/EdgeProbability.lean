/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.UpperEdgeGeometry

/-!
# Edge entrance probabilities from independent finite prefixes

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_movingTransitionEvent_ge_positivePrefix_mul_transition`:
  for $x\in[0,\Delta/12]$, the moving entrance probability is at least
  $\nu([a,b])^m\mathbb P(D_{N,\Delta})$ under the lower-edge geometry.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_movingTransitionEvent_ge_negativePrefix_mul_reflectedTransition`:
  for $x\in[11\Delta/12,\Delta]$, the analogous bound uses the law
  of the reflected increments.

These are the independent-prefix probability steps in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The lower-edge moving entrance event contains the product event
formed by a positive increment prefix and an independent transition suffix. -/
theorem measure_movingTransitionEvent_ge_positivePrefix_mul_transition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc 0 (width / 12))
    (hprefixHeight : drift ≤ (m : ℝ) * a)
    (hprefixUpper : 12 * (m : ℝ) * b ≤ width)
    (hstep : drift ≤ a * width ^ 2)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2) :
    (ν (Set.Icc a b)) ^ m *
        iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) ≤
      iidSequenceLaw ν (movingTransitionEvent (m + N) width drift start) := by
  calc
    (ν (Set.Icc a b)) ^ m *
        iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) =
        iidSequenceLaw ν
          {increment | (∀ k < m, increment k ∈ Set.Icc a b) ∧
            (fun k => increment (m + k)) ∈
              FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} :=
      (FunctionalLimit.Conditioned.measure_prefixWindow_and_shiftedTransition
        ν (Set.Icc a b) measurableSet_Icc m N width).symm
    _ ≤ iidSequenceLaw ν
          (movingTransitionEvent (m + N) width drift start) :=
      measure_mono
        (prefixPositiveWindow_and_transition_subset_movingTransitionEvent
          hwidth hdrift ha hab hstart hprefixHeight hprefixUpper hstep htotal)

/-- The upper-edge moving entrance event contains the product event
formed by a negative increment prefix and a reflected transition suffix. -/
theorem measure_movingTransitionEvent_ge_negativePrefix_mul_reflectedTransition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc (11 / 12 * width) width)
    (hprefixUpper : 24 * (m : ℝ) * b ≤ width)
    (hsmallDrift : 24 * drift ≤ width)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2) :
    ((ν.map fun x : ℝ => -x) (Set.Icc a b)) ^ m *
        iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) ≤
      iidSequenceLaw ν (movingTransitionEvent (m + N) width drift start) := by
  calc
    ((ν.map fun x : ℝ => -x) (Set.Icc a b)) ^ m *
        iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) =
        iidSequenceLaw ν
          {increment | (∀ k < m, -increment k ∈ Set.Icc a b) ∧
            (fun k => -increment (m + k)) ∈
              FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} :=
      (FunctionalLimit.Conditioned.measure_reflectedPrefixWindow_and_shiftedTransition
        ν (Set.Icc a b) measurableSet_Icc m N width).symm
    _ ≤ iidSequenceLaw ν
          (movingTransitionEvent (m + N) width drift start) :=
      measure_mono
        (prefixNegativeWindow_and_reflectedTransition_subset_movingTransitionEvent
          hwidth hdrift ha hab hstart hprefixUpper hsmallDrift htotal)

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
