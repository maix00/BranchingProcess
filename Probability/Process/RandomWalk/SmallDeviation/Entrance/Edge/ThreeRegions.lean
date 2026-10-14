/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Edge.Probability
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.MovingInterior

/-!
# The three starting-point intervals of the entrance proof

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_movingTransitionEvent_ge_threeRegionMinimum`:
  the middle interval and the two edge intervals cover $[0,\Delta]$;
  the minimum of their three probability bounds applies uniformly
  to every start $x\in[0,\Delta]$.

This is the final three-interval step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The minimum of the middle and two edge estimates controls the moving
entrance event for every initial point in the whole width interval. -/
theorem measure_movingTransitionEvent_ge_threeRegionMinimum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n mPlus NPlus mMinus NMinus : ℕ}
    {width drift aPlus bPlus aMinus bMinus : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2) (hlarge : 12 * drift ≤ width)
    (hplusLength : n = mPlus + NPlus)
    (hminusLength : n = mMinus + NMinus)
    (haPlus : 0 < aPlus) (habPlus : aPlus ≤ bPlus)
    (hplusHeight : drift ≤ (mPlus : ℝ) * aPlus)
    (hplusUpper : 12 * (mPlus : ℝ) * bPlus ≤ width)
    (hplusStep : drift ≤ aPlus * width ^ 2)
    (haMinus : 0 < aMinus) (habMinus : aMinus ≤ bMinus)
    (hminusUpper : 24 * (mMinus : ℝ) * bMinus ≤ width)
    (hminusDrift : 24 * drift ≤ width)
    {middleBound : ℝ≥0∞}
    (hmiddle : ∀ start ∈ Set.Icc (width / 12) (11 / 12 * width),
      middleBound ≤ iidSequenceLaw ν
        (FunctionalLimit.Donsker.finiteInteriorEvent n width drift start))
    (start : ℝ) (hstart : start ∈ Set.Icc 0 width) :
    min middleBound
        (min
          ((ν (Set.Icc aPlus bPlus)) ^ mPlus *
            iidSequenceLaw ν
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                NPlus width))
          (((ν.map fun x : ℝ => -x) (Set.Icc aMinus bMinus)) ^ mMinus *
            iidSequenceLaw (ν.map fun x : ℝ => -x)
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                NMinus width))) ≤
      iidSequenceLaw ν (movingTransitionEvent n width drift start) := by
  by_cases hleft : start ≤ width / 12
  · have hbound :=
      measure_movingTransitionEvent_ge_positivePrefix_mul_transition
        (m := mPlus) (N := NPlus) ν hwidth hdrift haPlus habPlus ⟨hstart.1, hleft⟩
        hplusHeight hplusUpper hplusStep (by simpa [← hplusLength] using hn)
    rw [← hplusLength] at hbound
    exact (min_le_right _ _).trans ((min_le_left _ _).trans hbound)
  by_cases hright : 11 / 12 * width ≤ start
  · have hbound :=
      measure_movingTransitionEvent_ge_negativePrefix_mul_reflectedTransition
        (m := mMinus) (N := NMinus) ν hwidth hdrift haMinus habMinus ⟨hright, hstart.2⟩
        hminusUpper hminusDrift (by simpa [← hminusLength] using hn)
    rw [← hminusLength] at hbound
    exact (min_le_right _ _).trans ((min_le_right _ _).trans hbound)
  have hmiddleStart : start ∈ Set.Icc (width / 12) (11 / 12 * width) := by
    exact ⟨le_of_lt (lt_of_not_ge hleft),
      le_of_lt (lt_of_not_ge hright)⟩
  exact (min_le_left _ _).trans
    ((hmiddle start hmiddleStart).trans
      (measure_mono
        (finiteInteriorEvent_subset_movingTransitionEvent
          hwidth hdrift hn hlarge)))

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
