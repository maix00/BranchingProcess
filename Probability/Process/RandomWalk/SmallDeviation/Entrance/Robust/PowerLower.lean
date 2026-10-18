/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.BlockScale
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.MiddleProbability
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.ThreeRegions
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Edge.PrefixSelection
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.Edge.PrefixGeometry
/-!
# Power lower bound for the robust entrance event

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_robustTransitionProbability_ge_power_of_transitionBounds`:
  if the forward and reflected nonnegative-transition events at
  $\lfloor a_n^2\rfloor-m$ each have an eventual lower bound of the form
  $C_\pm a_n^{-1-\alpha}$ for every fixed $m$, where $a_n\to\infty$ and
  $\alpha>0$, then the robust moving entrance event has an eventual lower
  bound $C a_n^{-1-\alpha}$ uniformly for starting points in $[0,a_n]$.

This is the final minimum-of-three-intervals step in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7, used in the proof of Chapter 3, Lemma 3.5. `FunctionalLimit/Conditioned/Transition/DiffusiveLower.lean`
supplies the inverse-square transition bound from the conditioned
Brownian-meander limit and the cyclic-rotation survival inequality.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The middle Donsker bound and the two meander-transition bounds combine
to give the power lower bound for the robust moving entrance event. -/
lemma exists_eventually_robustTransitionProbability_ge_power_of_transitionBounds
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift alpha : ℝ} (hdrift : 0 ≤ drift) (halpha : 0 < alpha)
    (hplus : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal)
    (hminus : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc 0 (width n),
        C / width n ^ (1 + alpha) ≤
          (iidSequenceLaw ν
            (robustMovingTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
              (width n) drift start)).toReal := by
  obtain ⟨aPlus, bPlus, aMinus, bMinus, mPlus, mMinus,
    haPlus, habPlus, hpPlus, haMinus, habMinus, hpMinus,
    hmPlus, hmMinus⟩ :=
    exists_positive_mass_prefixes hν hsigma drift
  obtain ⟨CPlus, hCPlus, hplusEventually⟩ := hplus mPlus
  obtain ⟨CMinus, hCMinus, hminusEventually⟩ := hminus mMinus
  obtain ⟨q, hq, hmiddleEventually⟩ :=
    eventually_middleRobustTransitionProbability_pos
      hν hsigma hwidth hdrift
  let q' : ℝ≥0∞ := min q 1
  have hq' : 0 < q' := lt_min hq (by norm_num)
  have hq'finite : q' ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right q 1) (by simp))
  have hpPlusFinite : ν (Set.Icc aPlus bPlus) ≠ ⊤ := measure_ne_top _ _
  have hpMinusFinite :
      (ν.map fun x : ℝ => -x) (Set.Icc aMinus bMinus) ≠ ⊤ :=
    measure_ne_top _ _
  let pPlus : ℝ≥0∞ := ν (Set.Icc aPlus bPlus)
  let pMinus : ℝ≥0∞ :=
    (ν.map fun x : ℝ => -x) (Set.Icc aMinus bMinus)
  let C : ℝ := min q'.toReal
    (min (pPlus.toReal ^ mPlus * CPlus)
      (pMinus.toReal ^ mMinus * CMinus))
  have hC : 0 < C := by
    dsimp [C]
    apply lt_min
    · exact ENNReal.toReal_pos hq'.ne' hq'finite
    apply lt_min
    · exact mul_pos (pow_pos (ENNReal.toReal_pos hpPlus.ne' hpPlusFinite) _) hCPlus
    · exact mul_pos (pow_pos (ENNReal.toReal_pos hpMinus.ne' hpMinusFinite) _) hCMinus
  refine ⟨C, hC, ?_⟩
  have hgeometry := eventually_prefix_geometry hwidth haPlus mPlus mMinus
    (drift := drift) (bPlus := bPlus) (bMinus := bMinus)
  have hwidthOne : ∀ᶠ n : ℕ in atTop, 1 ≤ width n :=
    hwidth.eventually (eventually_ge_atTop 1)
  have hsmallEventually : ∀ᶠ n : ℕ in atTop,
      max (120 * (mPlus : ℝ) * bPlus)
        (120 * ((mMinus : ℝ) * bMinus + drift)) ≤ width n :=
    hwidth.eventually (eventually_ge_atTop _)
  filter_upwards [hplusEventually, hminusEventually, hmiddleEventually,
    hgeometry, hwidthOne, hsmallEventually] with n hnPlus hnMinus
      hnMiddle hnGeo hnOne hnSmall
  intro start hstart
  let length := Asymptotics.floorBlockLength (fun k => width k ^ 2) n
  have hlengthPlus : length = mPlus + (length - mPlus) := by omega
  have hlengthMinus : length = mMinus + (length - mMinus) := by omega
  have hfloor : (length : ℝ) ≤ width n ^ 2 :=
    Nat.floor_le (sq_nonneg _)
  have hmiddle : ∀ x ∈ Set.Icc (width n / 12) (11 / 12 * width n),
      q' ≤ iidSequenceLaw ν
        (robustMovingTransitionEvent
          length (width n) drift x) := by
    intro x hx
    exact (min_le_left _ _).trans (hnMiddle x hx)
  have hplusSmall :
      120 * (mPlus : ℝ) * bPlus ≤ 7 * width n := by
    have h := (le_max_left _ _).trans hnSmall
    nlinarith [hnGeo.1]
  have hminusSmall :
      120 * ((mMinus : ℝ) * bMinus + drift) ≤ 5 * width n := by
    have h := (le_max_right _ _).trans hnSmall
    nlinarith [hnGeo.1]
  have hthree :=
    measure_robustMovingTransitionEvent_ge_threeRegionMinimum ν
      hnGeo.1 hdrift hfloor
      hlengthPlus hlengthMinus
      haPlus habPlus.le
      (by linarith [hmPlus] : drift ≤ (mPlus : ℝ) * aPlus)
      hnGeo.2.2.1 hnGeo.2.2.2.2.2.1 hplusSmall
      haMinus habMinus.le
      hnGeo.2.2.2.1 hnGeo.2.2.2.2.1 hminusSmall
      hmiddle start hstart
  have hthreeReal := ENNReal.toReal_mono (measure_ne_top _ _) hthree
  have hpow : 0 < width n ^ (1 + alpha) :=
    Real.rpow_pos_of_pos hnGeo.1 _
  have hpowOne : 1 ≤ width n ^ (1 + alpha) := by
    exact Real.one_le_rpow hnOne (by linarith)
  have hmiddlePower : C / width n ^ (1 + alpha) ≤ q'.toReal := by
    have hbound : C ≤ q'.toReal := min_le_left _ _
    calc
      C / width n ^ (1 + alpha) ≤ q'.toReal / width n ^ (1 + alpha) :=
        div_le_div_of_nonneg_right hbound hpow.le
      _ ≤ q'.toReal := by
        exact (div_le_iff₀ hpow).2
          (by nlinarith [ENNReal.toReal_nonneg (a := q')])
  have hplusPower : C / width n ^ (1 + alpha) ≤
      pPlus.toReal ^ mPlus *
        (iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (length - mPlus) (width n))).toReal := by
    have hbound : C ≤ pPlus.toReal ^ mPlus * CPlus :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hpNonneg : 0 ≤ pPlus.toReal ^ mPlus := pow_nonneg ENNReal.toReal_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hnPlus hpNonneg
    calc
      C / width n ^ (1 + alpha) ≤
          (pPlus.toReal ^ mPlus * CPlus) / width n ^ (1 + alpha) :=
        div_le_div_of_nonneg_right hbound hpow.le
      _ = pPlus.toReal ^ mPlus * (CPlus / width n ^ (1 + alpha)) := by ring
      _ ≤ _ := hmul
  have hminusPower : C / width n ^ (1 + alpha) ≤
      pMinus.toReal ^ mMinus *
        (iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (length - mMinus) (width n))).toReal := by
    have hbound : C ≤ pMinus.toReal ^ mMinus * CMinus :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hpNonneg : 0 ≤ pMinus.toReal ^ mMinus := pow_nonneg ENNReal.toReal_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hnMinus hpNonneg
    calc
      C / width n ^ (1 + alpha) ≤
          (pMinus.toReal ^ mMinus * CMinus) / width n ^ (1 + alpha) :=
        div_le_div_of_nonneg_right hbound hpow.le
      _ = pMinus.toReal ^ mMinus * (CMinus / width n ^ (1 + alpha)) := by ring
      _ ≤ _ := hmul
  have hminimum : C / width n ^ (1 + alpha) ≤
      min q'.toReal
        (min
          (pPlus.toReal ^ mPlus *
            (iidSequenceLaw ν
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                (length - mPlus) (width n))).toReal)
          (pMinus.toReal ^ mMinus *
            (iidSequenceLaw (ν.map fun x : ℝ => -x)
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                (length - mMinus) (width n))).toReal)) :=
    le_min hmiddlePower (le_min hplusPower hminusPower)
  have hplusFinite :
      pPlus ^ mPlus *
        iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (length - mPlus) (width n)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hpPlusFinite) (measure_ne_top _ _)
  have hminFinite :
      min
        (pPlus ^ mPlus *
          iidSequenceLaw ν
            (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
              (length - mPlus) (width n)))
        (pMinus ^ mMinus *
          iidSequenceLaw (ν.map fun x : ℝ => -x)
            (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
              (length - mMinus) (width n))) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_left _ _)
      (lt_top_iff_ne_top.mpr hplusFinite))
  have hconverted :
      min q'.toReal
        (min
          (pPlus.toReal ^ mPlus *
            (iidSequenceLaw ν
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                (length - mPlus) (width n))).toReal)
          (pMinus.toReal ^ mMinus *
            (iidSequenceLaw (ν.map fun x : ℝ => -x)
              (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
                (length - mMinus) (width n))).toReal)) ≤
      (iidSequenceLaw ν
        (robustMovingTransitionEvent length (width n) drift start)).toReal := by
    simpa only [pPlus, pMinus, ENNReal.toReal_min hq'finite hminFinite,
      ENNReal.toReal_min hplusFinite
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top hpMinusFinite)
          (measure_ne_top _ _)), ENNReal.toReal_mul,
      ENNReal.toReal_pow] using hthreeReal
  exact hminimum.trans hconverted

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
