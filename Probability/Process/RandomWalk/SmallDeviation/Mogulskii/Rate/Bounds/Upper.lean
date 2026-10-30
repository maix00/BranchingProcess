/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Process.Brownian.SmallDeviation.Range.UpperRate
import Probability.Process.RandomWalk.Kernel.Killed.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
public import Analysis.Asymptotics.Scale.Block.Diffusive
public import Probability.Sequence.IID.Basic

import Probability.Process.RandomWalk.Kernel.Killed.Survival.Blocking
import Probability.Process.RandomWalk.Path.Block.Oscillation
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.UpperBound
import Probability.Sequence.Block
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Bounds.Lemmas.SharpUpper.BlockEstimate
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Bounds.Lemmas.EndpointCLT

/-!
# Horizontal-tube upper bounds

For a walk that stays in a fixed-width interval, its displacement over a
complete block must lie in an interval whose length is at most twice the
corridor width.  The diffusive endpoint CLT therefore gives a uniform
strictly subunit upper bound for one block whenever the limiting Gaussian
puts less mass on that displacement interval than the chosen bound.  Kernel
blocking then gives an exponential upper bound over arbitrary durations.

The fixed-cover theorem also gives a bound uniform over the tube offset
$a\in[0,1]$. It combines the block Donsker estimate with a finite Brownian
corridor cover, as in A. A. Mogul'skii, Theorem 3, Section 4, p. 764.

This endpoint estimate gives a strict exponential upper rate. The sharp
constant uses the path-level small-deviation rate in Theorem 3, Section 4,
p. 764, of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_horizontalTubeProbability_le_pow_diffusiveBlockCount`:
  for centered unit-variance increments and $0<a<1$, the horizontal-tube
  probability is eventually at most $q^{\lfloor n/b_n\rfloor}$, where $b_n$
  is the diffusive block length.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_horizontalTubeProbability_le_pow_fixedCover_uniformOffset`:
  for every offset $a\in[0,1]$, a fixed finite Brownian corridor cover gives
  an eventual power bound for the horizontal-tube probability.

The fixed-cover estimate uses the continuous-path Donsker theorem formalized
as `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_brownian`,
corresponding to Theorem 4.20 in I. Karatzas and S. E. Shreve, *Brownian
Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113,
Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal
open ProbabilityTheory.Process.Path
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.Process.Brownian.SmallDeviation.Range


/-- The endpoint-CLT row bound controls survival over every number of steps.
The exponent is the number of complete diffusive blocks; an incomplete final
block is discarded by the sub-Markov comparison. -/
theorem eventually_horizontalTubeProbability_le_pow_diffusiveBlockCount
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {a constant q : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hconstant : 0 < constant)
    (hgaussian : (gaussianReal 0 1).map
        (fun z : ℝ => z * Real.sqrt constant)
        (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal q) :
    ∀ᶠ n : ℕ in atTop,
      horizontalTubeProbability (iidSequenceLaw ν) a (scale n) n ≤
        ENNReal.ofReal q ^ (n / Asymptotics.diffusiveBlockLength constant scale n) := by
  have hrow := eventually_uniform_killedBlock_remainingMass_le_of_endpointCLT
    ν hcentered hsecondMoment hscale (-a) (1 - a) constant q hconstant
    (by simpa using hgaussian)
  filter_upwards [hrow, _root_.Asymptotics.IsSmallDeviationScale.eventually_pos hscale,
      _root_.Asymptotics.IsSmallDeviationScale.eventually_diffusiveBlockLength_pos hscale hconstant]
    with n hnRow hnScale hnBlock
  have hnRow' : ∀ x : Set.Icc ((-a) * scale n) ((1 - a) * scale n),
      Kernel.remainingMass
          (killedIncrementKernelOn ν
            (Set.Icc ((-a) * scale n) ((1 - a) * scale n)) measurableSet_Icc)
          (Asymptotics.diffusiveBlockLength constant scale n) x ≤ ENNReal.ofReal q := by
    simpa only using hnRow
  have hbound := Kernel.remainingMass_le_pow_div
    (killedIncrementKernelOn ν
      (Set.Icc ((-a) * scale n) ((1 - a) * scale n)) measurableSet_Icc)
    (Asymptotics.diffusiveBlockLength constant scale n) n
    ⟨0, by constructor <;> nlinarith⟩ (ENNReal.ofReal q) hnRow'
  rw [← remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
    ν a (scale n) ha0.le ha1.le hnScale.le n]
  simpa [neg_mul] using hbound

/-- The fixed-cover upper bound is uniform in the location of the horizontal
tube.  The offset `a` parametrizes the interval `[-a * scale n,
(1-a) * scale n]`, so this is the translated-width form needed when a walk is
known to stay in a spatial interval whose position depends on its past. -/
theorem eventually_horizontalTubeProbability_le_pow_fixedCover_uniformOffset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant enlargement : ℝ} {count : ℕ}
    (hconstant : 0 < constant) (henlargement : 0 < enlargement)
    (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        horizontalTubeProbability (iidSequenceLaw ν)
          a (scale n) n ≤
        ENNReal.ofReal (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) ^
          (n / Asymptotics.diffusiveBlockLength constant scale n) := by
  have hblock := eventually_diffusiveBlockOscillationProbability_le_of_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hconstant henlargement hcount hspectral
  filter_upwards [hblock,
    _root_.Asymptotics.IsSmallDeviationScale.eventually_pos hscale,
    _root_.Asymptotics.IsSmallDeviationScale.eventually_diffusiveBlockLength_pos hscale hconstant]
    with n hblock hscalePos hlengthPos
  intro a ha0 ha1
  have hhorizontal := horizontalTubeProbability_le_pow_blockOscillation
    ν ha0 ha1 hscalePos.le (Asymptotics.diffusiveBlockLength constant scale n) n
  have hpow :
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (scale n) (Asymptotics.diffusiveBlockLength constant scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (Asymptotics.diffusiveBlockLength constant scale n) increment)}) ^
          (n / Asymptotics.diffusiveBlockLength constant scale n) ≤
        ENNReal.ofReal (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) ^
            (n / Asymptotics.diffusiveBlockLength constant scale n) := by
    gcongr
  exact hhorizontal.trans (hpow.trans_eq (by rfl))


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
