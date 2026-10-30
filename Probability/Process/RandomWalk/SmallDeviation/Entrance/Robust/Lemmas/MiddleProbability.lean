/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event
import Probability.Process.RandomWalk.SmallDeviation.Entrance.FiniteVariance.InteriorDiffusive
/-!
# Proof support for the robust entrance event

## Internal proof declarations

The supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_middleRobustTransitionProbability_pos`:
  for a centered increment law with variance $\sigma^2>0$, $c\ge0$, and
  $\Delta_n\to\infty$, one constant $q>0$ bounds below the probability of
  the moving corridor with terminal window
  $[h_n+2\Delta_n/5,h_n+3\Delta_n/5]$, uniformly over
  $x\in[\Delta_n/12,11\Delta_n/12]$ for all sufficiently large $n$.

This is the middle-start step of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Appendix A.2, Lemma A.7, used in Chapter 3, Lemma 3.5.
It is an internal step in the three-region proof of the robust entrance
estimate.
-/

section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The diffusive interior event is contained in the robust moving transition
event once the drift displacement is small compared with the width. -/
private lemma finiteInteriorEvent_subset_robustMovingTransitionEvent
    {n : ℕ} {width drift start : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2)
    (hlarge : 60 * drift ≤ width) :
    FiniteVariance.finiteInteriorEvent n width drift start ⊆
      robustMovingTransitionEvent n width drift start := by
  intro increment hinc
  have hsq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hmove : increment ∈ movingCorridorEvent n width drift start := by
    unfold movingCorridorEvent
    intro k
    have hkNat : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have hk : (((k.val + 1 : ℕ) : ℝ)) ≤ width ^ 2 :=
      (Nat.cast_le.mpr hkNat).trans hn
    have hshiftNonneg :
        0 ≤ drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 :=
      div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hsq.le
    have hshiftLe :
        drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤ drift := by
      apply (div_le_iff₀ hsq).2
      exact mul_le_mul_of_nonneg_left hk hdrift
    have hgrid := hinc.1 k
    exact ⟨hshiftLe.trans hgrid.1,
      hgrid.2.trans (le_add_of_nonneg_right hshiftNonneg)⟩
  have hshift : drift * (n : ℝ) / width ^ 2 ≤ drift := by
    exact (div_le_iff₀ hsq).2
      (mul_le_mul_of_nonneg_left hn hdrift)
  have hshiftNonneg : 0 ≤ drift * (n : ℝ) / width ^ 2 := by positivity
  refine ⟨hmove, ?_⟩
  exact ⟨by nlinarith [hinc.2.1, hshift, hlarge],
    by nlinarith [hinc.2.2, hshiftNonneg, hwidth]⟩

/-- Middle starting points reach the robust window with probability
bounded below uniformly at sufficiently large diffusive widths. -/
lemma eventually_middleRobustTransitionProbability_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift : ℝ} (hdrift : 0 ≤ drift) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (robustMovingTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
            (width n) drift start) := by
  obtain ⟨q, hq, hmiddle⟩ :=
    FiniteVariance.eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment
      hν hsigma hwidth drift
  refine ⟨q, hq, ?_⟩
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hwidthLarge : ∀ᶠ n : ℕ in atTop, 60 * drift ≤ width n := by
    filter_upwards [hwidth.eventually
      (eventually_ge_atTop (60 * drift))] with n hn
    exact hn
  filter_upwards [hmiddle, hwidthPos, hwidthLarge] with n hn hw hl
  intro start hs
  have hfloor :
      ((Asymptotics.floorBlockLength (fun k => width k ^ 2) n : ℕ) : ℝ) ≤
        width n ^ 2 := Nat.floor_le (sq_nonneg _)
  exact (hn start hs).trans (measure_mono
    (finiteInteriorEvent_subset_robustMovingTransitionEvent
      hw hdrift hfloor hl))

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
