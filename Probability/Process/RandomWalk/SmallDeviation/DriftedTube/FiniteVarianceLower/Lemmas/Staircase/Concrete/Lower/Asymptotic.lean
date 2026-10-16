/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.Lower.Global
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Eventually
/-!
# Asymptotic finite-staircase lower bound

The public theorem in this file is:

- `eventually_concreteStaircaseLowerBound_of_robustEntrance`:
  along widths $\Delta_n\to\infty$ and arbitrary starting boundaries
  $r_{0,n}$, with
  $\Delta_n^2/\ell_n\to0$ and $\ell_n/\Delta_n^3\to0$,
  the robust entrance probability budget and fixed rate and endpoint
  margins imply the eventual tilted-tube lower bound
  $\mathbb P(E_n)\ge\exp(-d'L_n/\Delta_n^2)$.

This is the staircase multiplication in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The entrance probability is the one
established in Appendix A.2 by the Brownian-meander argument.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The exact concrete staircase bound holds eventually once the robust
entrance estimate from Appendix A.2 is supplied. -/
lemma eventually_concreteStaircaseLowerBound_of_robustEntrance
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma narrowedRate uInterior vInterior uFinal vFinal : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huFinal : 0 < uFinal)
    (huvFinal : uFinal < vFinal)
    (hvFinal : vFinal < 1)
    (hrateMogulskii : (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate)
    {entrance horizon blockLength : ℕ → ℕ}
    {width base : ℕ → ℝ}
    {margin drift endpointFraction blockRate totalRate : ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hlength : ∀ᶠ n : ℕ in atTop, 0 < blockLength n)
    (hremaining : ∀ᶠ n : ℕ in atTop,
      entrance n + 2 * blockLength n ≤ horizon n)
    (hquadratic : Tendsto (fun n =>
      width n ^ 2 / (blockLength n : ℝ)) atTop (𝓝 0))
    (hcubic : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0))
    (hmargin : 0 < margin)
    (hdrift : 0 ≤ drift)
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (hrate : narrowedRate < blockRate * staircaseBinWidth m ^ 2)
    (hinteriorLower : (1 / 3 : ℝ) / staircaseBinWidth m +
      margin < uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hfinalLower : margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hentrance : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(totalRate - blockRate) * (horizon n : ℝ) /
        width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (robustMovingTransitionEvent (entrance n) (width n)
            drift (-base n))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-totalRate * (horizon n : ℝ) / width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent (horizon n) (width n)
            drift (base n) endpointFraction) := by
  obtain ⟨width₀, ratio₀, hfinite⟩ :=
    exists_concreteStaircaseLowerBound_of_globalConditions
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrateMogulskii
  have hglobal := eventually_staircaseGlobalConditions m hm
    hwidth hlength hquadratic hcubic hrate hinteriorLower
    hinteriorUpper hfinalLower hfinalUpper width₀ ratio₀
    (drift := drift)
  filter_upwards [hremaining, hglobal, hentrance]
    with n hnRemaining hnGlobal hnEntrance
  obtain ⟨hnWidth, hnLength, hnCost, hnFloor, hnMargin,
    hnTime, hnRate, hnLower, hnUpper, hnFinalLower,
    hnFinalUpper⟩ := hnGlobal
  exact hfinite (entrance n) (horizon n) (blockLength n)
    margin (width n) drift (base n) endpointFraction blockRate totalRate
    hnRemaining hnLength hnWidth hmargin hdrift hendpoint hblockRate
    hnCost hnFloor hnMargin hnTime hnRate hnLower hnUpper
    hnFinalLower hnFinalUpper hnEntrance

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
