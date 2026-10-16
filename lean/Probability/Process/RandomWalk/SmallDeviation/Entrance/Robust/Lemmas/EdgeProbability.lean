/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.EdgeGeometry
/-!
# Edge probabilities for the robust entrance window

The public theorems in this file are:

- `measure_robustMovingTransitionEvent_ge_positivePrefix_mul_transition`:
  from $x\in[0,\Delta/12]$, the entrance probability is at least
  $\nu([a,b])^m\mathbb P(D_{N,\Delta})$.
- `measure_robustMovingTransitionEvent_ge_negativePrefix_mul_reflectedTransition`:
  from $x\in[11\Delta/12,\Delta]$, the reflected increment law gives the
  analogous product lower bound.

These are the independent-prefix products in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma, with the robust
terminal interval needed by the first staircase block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- A positive fixed prefix and its independent meander suffix yield the
robust entrance probability at the lower boundary. -/
lemma measure_robustMovingTransitionEvent_ge_positivePrefix_mul_transition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc 0 (width / 12))
    (hprefixHeight : drift ≤ (m : ℝ) * a)
    (hprefixUpper : 12 * (m : ℝ) * b ≤ width)
    (hstep : drift ≤ a * width ^ 2)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2)
    (hsmallPrefix : 120 * (m : ℝ) * b ≤ 7 * width) :
    (ν (Set.Icc a b)) ^ m *
        iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) ≤
      iidSequenceLaw ν
        (robustMovingTransitionEvent (m + N) width drift start) := by
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
          (robustMovingTransitionEvent (m + N) width drift start) :=
      measure_mono
        (prefixPositiveWindow_and_transition_subset_robustMovingTransitionEvent
          hwidth hdrift ha hab hstart hprefixHeight hprefixUpper hstep
          htotal hsmallPrefix)

/-- A negative fixed prefix and its reflected independent suffix yield
the robust entrance probability at the upper boundary. -/
lemma measure_robustMovingTransitionEvent_ge_negativePrefix_mul_reflectedTransition
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc (11 / 12 * width) width)
    (hprefixUpper : 24 * (m : ℝ) * b ≤ width)
    (hsmallDrift : 24 * drift ≤ width)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2)
    (hsmallSum : 120 * ((m : ℝ) * b + drift) ≤ 5 * width) :
    ((ν.map fun x : ℝ => -x) (Set.Icc a b)) ^ m *
        iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width) ≤
      iidSequenceLaw ν
        (robustMovingTransitionEvent (m + N) width drift start) := by
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
          (robustMovingTransitionEvent (m + N) width drift start) :=
      measure_mono
        (prefixNegativeWindow_and_reflectedTransition_subset_robustMovingTransitionEvent
          hwidth hdrift ha hab hstart hprefixUpper hsmallDrift htotal hsmallSum)

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
