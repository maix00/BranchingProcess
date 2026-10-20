/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Distributions.Moments.Real
public import Probability.Sequence.Filtration
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning
public import Probability.Process.RandomWalk.Path.Block.Partition.TailMerged
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.BlockTube
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointEvent
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.Lower.Asymptotic
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.EntranceBudget
public import Analysis.Asymptotics.Scale.Power.IntermediateBlock

/-!
# Tilted-tube lower bound from the reflected survival asymptotics

The module-visible supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.eventually_concreteStaircaseLowerBound_of_powerBlock`: the same bound
  with $\ell_n=\lfloor\Delta_n^{2+\eta}\rfloor$ and
  $0<\eta<\min(1,\varepsilon)$, so the scale limits and remaining-time
  condition follow from $\Delta_n\to\infty$ and
  $L_n\ge\lfloor\Delta_n^{2+\varepsilon}\rfloor$.

This is the composition of the entrance argument and the staircase
product in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. The two
transition estimates follow from the conditioned Brownian-meander limit
and the cyclic rotation cover in M. Bauer, C. Godrèche,
and J.-M. Luck, *Statistics of persistent events in the binomial random
walk: Will the drunken sailor hit the sober man?*, Appendix A,
immediately after (A.3) (arXiv:cond-mat/9905252).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The inverse-square survival inputs for the walk and its reflection follow from
the finite-variance hypotheses. -/
private lemma eventually_concreteStaircaseLowerBound_of_centeredFiniteVariance
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
    {horizon blockLength : ℕ → ℕ}
    {width base : ℕ → ℝ}
    {margin drift endpointFraction blockRate totalRate
      epsilon : ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hlength : ∀ᶠ n : ℕ in atTop, 0 < blockLength n)
    (hremaining : ∀ᶠ n : ℕ in atTop,
      Nat.floor (width n ^ 2) + 2 * blockLength n ≤ horizon n)
    (hhorizon : ∀ᶠ n : ℕ in atTop,
      Nat.floor (width n ^ (2 + epsilon)) ≤ horizon n)
    (hquadratic : Tendsto (fun n =>
      width n ^ 2 / (blockLength n : ℝ)) atTop (𝓝 0))
    (hcubic : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0))
    (hmargin : 0 < margin)
    (hdrift : 0 ≤ drift)
    (hstart : ∀ᶠ n : ℕ in atTop,
      -base n ∈ Set.Icc 0 (width n))
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < totalRate - blockRate)
    (hrate : narrowedRate < blockRate * staircaseBinWidth m ^ 2)
    (hinteriorLower : (1 / 3 : ℝ) / staircaseBinWidth m +
      margin < uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hfinalLower : margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-totalRate * (horizon n : ℝ) / width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent (horizon n) (width n)
            drift (base n) endpointFraction) := by
  have hbudget :=
    exists_eventually_robustTransitionProbability_ge_exp_of_centeredFiniteVariance
      ν hν hsigma
      hwidth hdrift hdelta hepsilon
  have hentrance : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(totalRate - blockRate) * (horizon n : ℝ) /
        width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (robustMovingTransitionEvent
            (Nat.floor (width n ^ 2)) (width n) drift (-base n)) := by
    filter_upwards [hbudget, hstart, hhorizon]
      with n hnBudget hnStart hnHorizon
    simpa [Asymptotics.floorBlockLength] using
      hnBudget (-base n) hnStart (horizon n) hnHorizon
  exact eventually_concreteStaircaseLowerBound_of_robustEntrance
    hν hsigma m hm huInterior huvInterior hvInterior
    huFinal huvFinal hvFinal hrateMogulskii
    hwidth hlength hremaining hquadratic hcubic hmargin hdrift
    hendpoint hblockRate hrate hinteriorLower hinteriorUpper
    hfinalLower hfinalUpper hentrance

/-- Choose the staircase length as
$\ell_n=\lfloor\Delta_n^{2+\eta}\rfloor$; its scale conditions and its
fit inside $L_n\ge\lfloor\Delta_n^{2+\varepsilon}\rfloor$ follow from
$0<\eta<\min(1,\varepsilon)$. -/
lemma eventually_concreteStaircaseLowerBound_of_powerBlock
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
    {horizon : ℕ → ℕ} {width base : ℕ → ℝ}
    {margin drift endpointFraction blockRate totalRate epsilon eta : ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hhorizon : ∀ᶠ n : ℕ in atTop,
      Nat.floor (width n ^ (2 + epsilon)) ≤ horizon n)
    (heta : 0 < eta) (hetaOne : eta < 1) (hetaEpsilon : eta < epsilon)
    (hmargin : 0 < margin) (hdrift : 0 ≤ drift)
    (hstart : ∀ᶠ n : ℕ in atTop,
      -base n ∈ Set.Icc 0 (width n))
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < totalRate - blockRate)
    (hrate : narrowedRate < blockRate * staircaseBinWidth m ^ 2)
    (hinteriorLower : (1 / 3 : ℝ) / staircaseBinWidth m +
      margin < uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hfinalLower : margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-totalRate * (horizon n : ℝ) / width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent (horizon n) (width n)
            drift (base n) endpointFraction) := by
  let blockLength : ℕ → ℕ :=
    Asymptotics.floorBlockLength (fun n => width n ^ (2 + eta))
  have hscale := Asymptotics.intermediate_power_block_ratios
    hwidth heta hetaOne
  change Tendsto (fun n => width n ^ 2 / (blockLength n : ℝ))
      atTop (𝓝 0) ∧
    Tendsto (fun n => (blockLength n : ℝ) / width n ^ 3)
      atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop, 0 < blockLength n at hscale
  obtain ⟨hquadratic, hcubic, hlength⟩ := hscale
  have hfit := Asymptotics.eventually_intermediate_block_fits
    hwidth heta hetaEpsilon
  have hremaining : ∀ᶠ n : ℕ in atTop,
      Nat.floor (width n ^ 2) + 2 * blockLength n ≤ horizon n := by
    filter_upwards [hfit, hhorizon] with n hnfit hnHorizon
    exact hnfit.trans hnHorizon
  exact eventually_concreteStaircaseLowerBound_of_centeredFiniteVariance
    hν hsigma m hm huInterior huvInterior hvInterior
    huFinal huvFinal hvFinal hrateMogulskii hwidth hlength
    hremaining hhorizon hquadratic hcubic hmargin hdrift hstart
    hendpoint hblockRate hepsilon hdelta hrate
    hinteriorLower hinteriorUpper hfinalLower hfinalUpper

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
