/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Distributions.Moments.Real
public import Probability.Sequence.Filtration
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Binning.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Schedule
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.BlockTube
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.EndpointWindow
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointEvent
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Reflection
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.Upper.Global
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Eventually

/-!
# Asymptotic upper-endpoint staircase lower bound

The module-visible supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.eventually_concreteStaircaseUpperEndpointLowerBound_of_robustEntrance`:
  under the superquadratic and subcubic block scales of Wang Yiyang's Lemma 3.5, fixed
  endpoint and rate margins, and the robust entrance probability
  budget, the upper-endpoint event has probability at least
  $\exp(-d'L_n/\Delta_n^2)$ eventually.

This is the common-threshold symmetric construction in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The upper-endpoint staircase bound holds eventually once its robust
entrance estimate and fixed endpoint margins are supplied. -/
lemma eventually_concreteStaircaseUpperEndpointLowerBound_of_robustEntrance
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
    (hfinalLower : max (1 - endpointFraction) 0 /
        staircaseBinWidth m + margin < uFinal)
    (hfinalUpper : vFinal + margin ≤
      (1 - 1 / (3 * (m : ℝ))) /
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
          (driftedTubeUpperEndpointWindowEvent (horizon n) (width n)
            drift (base n) endpointFraction) := by
  obtain ⟨width₀, ratio₀, hfinite⟩ :=
    exists_concreteStaircaseUpperEndpointLowerBound_of_globalConditions
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrateMogulskii
  have hglobal := eventually_staircaseUpperEndpointGlobalConditions m hm
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
