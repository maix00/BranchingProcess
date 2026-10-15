/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Concrete.AsymptoticLower
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.RobustExponentialBudget

/-!
# Tilted-tube lower bound from the reflected survival asymptotics

The public theorem in this file is:

- `eventually_concreteStaircaseLowerBound_of_regularVariation`:
  for $t_1=\lfloor\Delta^2\rfloor$ and
  $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$, the two reflected
  survival regular-variation inputs from Appendix A.2, the paper's
  block-scale limits, and fixed endpoint and rate margins imply
  $\mathbb P(E)\ge\exp(-d'L/\Delta^2)$ eventually.

This is the composition of the entrance argument and the staircase
product in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, proof of Lemma 3.5. The two
transition estimates follow from the conditioned Brownian-meander limit
and the survival asymptotic in Caravenna--Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
equation (3.3) and Lemma 2.1, respectively.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The remaining fluctuation-theory inputs are the survival asymptotics
for the walk and its reflection. -/
theorem eventually_concreteStaircaseLowerBound_of_regularVariation
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma narrowedRate uInterior vInterior uFinal vFinal : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hregPlus : Asymptotics.IsRegularlyVaryingAtTop
      (FunctionalLimit.Conditioned.survivalProbabilityReal ν)
      (-(1 / 2 : ℝ)))
    (hregMinus : Asymptotics.IsRegularlyVaryingAtTop
      (FunctionalLimit.Conditioned.survivalProbabilityReal
        (ν.map fun x : ℝ => -x)) (-(1 / 2 : ℝ)))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huFinal : 0 < uFinal)
    (huvFinal : uFinal < vFinal)
    (hvFinal : vFinal < 1)
    (hrateMogulskii : (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate)
    {horizon blockLength : ℕ → ℕ}
    {width : ℕ → ℝ}
    {margin drift base endpointFraction blockRate totalRate
      alpha epsilon : ℝ}
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
    (hbase : base ≤ 0)
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (halpha : 0 < alpha)
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
            drift base endpointFraction) := by
  have hbudget :=
    exists_eventually_robustTransitionProbability_ge_exp_of_regularVariation
      ν hν hsigma hregPlus hregMinus hB hcontinuous hmeasurable
      hrho hrhoSmall hwidth hdrift halpha hdelta hepsilon
  have hstart : ∀ᶠ n : ℕ in atTop, -base ∈ Set.Icc 0 (width n) := by
    have hwide := hwidth.eventually (eventually_ge_atTop (-base))
    filter_upwards [hwide] with n hn
    exact ⟨by linarith, hn⟩
  have hentrance : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(totalRate - blockRate) * (horizon n : ℝ) /
        width n ^ 2) ≤
        (iidSequenceLaw ν).real
          (robustMovingTransitionEvent
            (Nat.floor (width n ^ 2)) (width n) drift (-base)) := by
    filter_upwards [hbudget, hstart, hhorizon]
      with n hnBudget hnStart hnHorizon
    simpa [Asymptotics.floorBlockLength] using
      hnBudget (-base) hnStart (horizon n) hnHorizon
  exact eventually_concreteStaircaseLowerBound_of_robustEntrance
    hν hsigma m hm huInterior huvInterior hvInterior
    huFinal huvFinal hvFinal hrateMogulskii
    hwidth hlength hremaining hquadratic hcubic hmargin hdrift
    hendpoint hblockRate hrate hinteriorLower hinteriorUpper
    hfinalLower hfinalUpper hentrance

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
