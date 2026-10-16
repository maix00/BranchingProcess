/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.EdgeProbability
/-!
# Three-region bound for a robust diffusive entrance

The module-visible supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measure_robustMovingTransitionEvent_ge_threeRegionMinimum`:
  the minimum of the middle Donsker bound and the two independent-prefix
  meander bounds applies uniformly to every $x\in[0,\Delta]$.

This is the three starting-region division in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7. The terminal window
is narrowed to the robust interval needed in Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The middle, lower-edge and upper-edge estimates give one bound on the
robust transition event for every allowed start. -/
lemma measure_robustMovingTransitionEvent_ge_threeRegionMinimum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n mPlus NPlus mMinus NMinus : ℕ}
    {width drift aPlus bPlus aMinus bMinus : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2)
    (hplusLength : n = mPlus + NPlus)
    (hminusLength : n = mMinus + NMinus)
    (haPlus : 0 < aPlus) (habPlus : aPlus ≤ bPlus)
    (hplusHeight : drift ≤ (mPlus : ℝ) * aPlus)
    (hplusUpper : 12 * (mPlus : ℝ) * bPlus ≤ width)
    (hplusStep : drift ≤ aPlus * width ^ 2)
    (hplusSmall : 120 * (mPlus : ℝ) * bPlus ≤ 7 * width)
    (haMinus : 0 < aMinus) (habMinus : aMinus ≤ bMinus)
    (hminusUpper : 24 * (mMinus : ℝ) * bMinus ≤ width)
    (hminusDrift : 24 * drift ≤ width)
    (hminusSmall :
      120 * ((mMinus : ℝ) * bMinus + drift) ≤ 5 * width)
    {middleBound : ℝ≥0∞}
    (hmiddle : ∀ start ∈ Set.Icc (width / 12) (11 / 12 * width),
      middleBound ≤ iidSequenceLaw ν
        (robustMovingTransitionEvent n width drift start))
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
      iidSequenceLaw ν (robustMovingTransitionEvent n width drift start) := by
  by_cases hleft : start ≤ width / 12
  · have hbound :=
      measure_robustMovingTransitionEvent_ge_positivePrefix_mul_transition
        (m := mPlus) (N := NPlus) ν hwidth hdrift haPlus habPlus
        ⟨hstart.1, hleft⟩ hplusHeight hplusUpper hplusStep
        (by simpa [← hplusLength] using hn) hplusSmall
    rw [← hplusLength] at hbound
    exact (min_le_right _ _).trans ((min_le_left _ _).trans hbound)
  by_cases hright : 11 / 12 * width ≤ start
  · have hbound :=
      measure_robustMovingTransitionEvent_ge_negativePrefix_mul_reflectedTransition
        (m := mMinus) (N := NMinus) ν hwidth hdrift haMinus habMinus
        ⟨hright, hstart.2⟩ hminusUpper hminusDrift
        (by simpa [← hminusLength] using hn) hminusSmall
    rw [← hminusLength] at hbound
    exact (min_le_right _ _).trans ((min_le_right _ _).trans hbound)
  have hmiddleStart : start ∈ Set.Icc (width / 12) (11 / 12 * width) :=
    ⟨le_of_lt (lt_of_not_ge hleft), le_of_lt (lt_of_not_ge hright)⟩
  exact (min_le_left _ _).trans (hmiddle start hmiddleStart)

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
