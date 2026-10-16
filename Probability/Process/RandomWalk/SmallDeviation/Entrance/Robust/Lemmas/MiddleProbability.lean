/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.Event
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Entrance.InteriorDiffusive
/-!
# Middle-start probability for the robust entrance event

The module-visible supporting lemma in this file is:

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

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

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
    FunctionalLimit.Donsker.Entrance.eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment
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
