/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Inverse
public import Probability.Sequence.IID.Basic
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.UpperBound
public import Probability.Process.RandomWalk.Path.Block.Partition.Range
import Probability.ConvergenceInDistribution.CadlagPath.RangeOscillation
/-!
# One-block corridors for the stable Mogulskii route

## Public declarations

The declarations in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockTube`:
  the event that an increment path stays in the open horizontal tube of
  width $w x_n$ for the stable block length.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableClosedBlockTube`:
  the corresponding closed-tube event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockCorridorProbability`:
  the i.i.d. probability of the open stable block tube.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube`:
  transfers the general Skorokhod range-oscillation bound to the source
  block-oscillation probability.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.eventually_openHorizontalTubeProbability_le_pow_of_blockPathLimit`:
  a one-block bound $q<1$ yields an eventual estimate
  $\mathbb P(T_n)\le q^{N_n/b_n}$ for horizon $N_n$ and block length $b_n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.eventually_partialSumRangeOscillationLTProbability_le_pow_of_blockPathLimit`:
  gives $\mathbb P(R_{N_n}<w x_n)\le q^{N_n/b_n}$ for the strict partial-sum
  range event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.measurableSet_stableClosedBlockTube`:
  the closed stable block tube is measurable.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockTube_mono_width`:
  decreasing the open tube width gives a subset of the original event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockCorridorProbability_mono_width`:
  the open-tube probability is monotone in its width.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockCorridorProbability_tendsto_of_pathLawLimit`:
  an explicit block-path $J_1$ limit and zero boundary mass give convergence
  of the open-tube probabilities.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.stableBlockCorridorProbability_tendsto_of_stableDomain`:
  stable-domain attraction, tightness, and slow variation provide the block
  path-law limit and hence the one-block corridor probability limit.

The one-block step of Mogulskii's stable proof estimates the probability that
the increment path stays in a corridor of normalized width `w` over a block
of `stableBlockLength α ν constant a n` steps, which is
`a n ^ α / L* (a n)` steps up to the constant factor `constant`. The
small-deviation scale `n * L* (a n) / a n ^ α` turns a per-block constant
into the corridor rate of the theorem.

For `α < 2`, the one-block limit is obtained from the stable Lévy process in
the Skorokhod `J₁` topology. At `α = 2`, the slowly varying factor is the
truncated second moment, and the block-length reduction to the diffusive scale is stated in
`Stable/Scale/IndexTwo.lean`.

The one-block estimate is conditional on the block path-law limit. The
general closed-range to open-tube bound is in
`Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block`; this
module specializes it to stable block lengths and applies independent-block
probability estimates.

The independent-block inequality used by the tube estimate is Mogul'skii's
Lemma 3(c), equation (32): a unit-horizon tube probability is bounded by the
corresponding one-block probability raised to the number of complete blocks.
The path-law comparison with the stable-process range tube is a separate
closed-set Portmanteau step. Source: A. A. Mogul'skii, “Small deviations in
the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755–765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI 10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory Set
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable



/-! ## The block corridor events -/

/-- The stable block corridor: after spatial normalization by `scale n`, the
increment path stays in the open corridor of normalized width `width` with
lower offset `a`, over a block of `stableBlockLength α ν constant scale n`
steps fixed by the increment law `ν`. -/
def stableBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    Set (ℕ → ℝ) :=
  {increment |
    InOpenHorizontalTube a (width * scale n)
      (stableBlockLength α ν constant scale n) increment}

/-- The closed variant of `stableBlockTube`, used by the upper bounds. -/
def stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ) (scale : ℕ → ℝ)
    (n : ℕ) : Set (ℕ → ℝ) :=
  {increment |
    InHorizontalTube a (width * scale n)
      (stableBlockLength α ν constant scale n) increment}

/-- The probability of the stable block corridor under the i.i.d. increment law. -/
noncomputable def stableBlockCorridorProbability (ν : Measure ℝ)
    (α constant a width : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  iidSequenceLaw ν (stableBlockTube ν α constant a width scale n)

/-- The one-block probability in Mogul'skii's discrete Lemma 3(c) is bounded
in the limit by the slightly wider stable-process range tube. This combines
the exact finite-block event bridge with closed-set Portmanteau. -/
theorem limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    (hc : 0 < c) (hmargin : 0 < margin) :
    atTop.limsup (fun n => iidSequenceLaw ν
      {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
        (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)}) ≤
      P (stableProcessTube ((width + margin) / (2 * c))) := by
  let finiteBlockProbability : ℕ → ENNReal := fun n => iidSequenceLaw ν
    {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
      (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)}
  let pathOscillationProbability : ℕ → ENNReal := fun n =>
    RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n
      (Skorokhod.rangeOscillationLe width)
  have hcompare : ∀ᶠ n in atTop,
      finiteBlockProbability n ≤ pathOscillationProbability n := by
    filter_upwards [hscale] with n hn
    simpa [finiteBlockProbability, pathOscillationProbability] using
      iidSequenceLaw_measure_blockOscillationLT_le_normalizedStepBlockPathLaw
        (ν := ν) scale blockLength n hn width
  have hpathBounded : Filter.IsBoundedUnder (· ≤ ·) atTop pathOscillationProbability := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [] with n
    calc
      pathOscillationProbability n ≤
          RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hlimsup := Filter.limsup_le_limsup hcompare
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)) hpathBounded
  have hstable :=
    MeasureTheory.TendstoInDistribution.limsup_measure_rangeOscillationLe_le_of_scalePath
      (width := width) hlimit hP.ae_start_eq_zero hc hmargin
  have hstable' : atTop.limsup pathOscillationProbability ≤
      P (stableProcessTube ((width + margin) / (2 * c))) := by
    simpa [pathOscillationProbability, RandomWalk.normalizedStepBlockPathLaw,
      ProbabilityTheory.stableProcessTube]
      using hstable
  change atTop.limsup finiteBlockProbability ≤ _
  exact hlimsup.trans hstable'

/-- The independent-block inequality and the fixed-parameter stable path
limit give an eventual exponential upper bound for an open horizontal
tube. The one-block base may be any strict upper bound on the slightly wider
stable range-tube probability. -/
theorem eventually_openHorizontalTubeProbability_le_pow_of_blockPathLimit
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {horizon blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hhorizon : ∀ᶠ n in atTop, 0 < horizon n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    (hc : 0 < c) (hwidth : 0 < width) (hmargin : 0 < margin)
    {q : ENNReal}
    (hq : P (stableProcessTube ((width + margin) / (2 * c))) < q) :
    ∀ᶠ n in atTop,
      openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (width * scale n) (horizon n) ≤ q ^ (horizon n / blockLength n) := by
  let finiteBlockProbability : ℕ → ENNReal := fun n => iidSequenceLaw ν
    {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
      (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)}
  have hlimsup := limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube
    (width := width) hP hscale hlimit hc hmargin
  have hprobabilityBounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop finiteBlockProbability := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [] with n
    calc
      finiteBlockProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hblockEventual : ∀ᶠ n in atTop, finiteBlockProbability n < q := by
    exact Filter.eventually_lt_of_limsup_lt
      (hlimsup.trans_lt hq) hprobabilityBounded
  filter_upwards [hblockEventual, hscale, hhorizon, hblock]
    with n hp hs hh hm
  have hsource :=
    openHorizontalTubeProbability_le_pow_blockOscillationLT_of_completeBlocks
      ν (a := (1 / 2 : ℝ)) (width := width * scale n)
      (by norm_num) (by norm_num) (mul_pos hwidth hs) (horizon n)
      (blockLength n) hh hm
  have hsource' : openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
      (width * scale n) (horizon n) ≤
        finiteBlockProbability n ^ (horizon n / blockLength n) := by
    simpa [finiteBlockProbability, Nat.floor_div_eq_div] using hsource
  calc
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (width * scale n) (horizon n) ≤
      finiteBlockProbability n ^ (horizon n / blockLength n) := by
        exact hsource'
    _ ≤ q ^ (horizon n / blockLength n) := by
      gcongr

/-- A strict range bound on a whole walk segment forces the strict
oscillation bound on each complete stable block. The one-block `J₁` limit
then gives the same eventual exponential estimate as for a centered tube,
without making any assumption about the segment's starting position. -/
theorem eventually_partialSumRangeOscillationLTProbability_le_pow_of_blockPathLimit
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {horizon blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    (hc : 0 < c) (hmargin : 0 < margin)
    {q : ENNReal}
    (hq : P (stableProcessTube ((width + margin) / (2 * c))) < q) :
    ∀ᶠ n in atTop,
      partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
        (width * scale n) (horizon n) ≤
          q ^ (horizon n / blockLength n) := by
  let finiteBlockProbability : ℕ → ENNReal := fun n => iidSequenceLaw ν
    {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
      (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)}
  have hlimsup := limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube
    (width := width) hP hscale hlimit hc hmargin
  have hprobabilityBounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop finiteBlockProbability := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [] with n
    calc
      finiteBlockProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hblockEventual : ∀ᶠ n in atTop, finiteBlockProbability n < q := by
    exact Filter.eventually_lt_of_limsup_lt
      (hlimsup.trans_lt hq) hprobabilityBounded
  filter_upwards [hblockEventual, hscale, hblock] with n hp hs hm
  have hsource :=
    ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_partialSumRangeLT_le_pow_blockOscillationLT_of_blockCover
      ν (width * scale n) (horizon n / blockLength n) (blockLength n)
      (horizon n) (Nat.div_mul_le_self (horizon n) (blockLength n))
  have hsource' :
      partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (width * scale n) (horizon n) ≤
        finiteBlockProbability n ^ (horizon n / blockLength n) := by
    simpa [partialSumRangeOscillationLTProbability, finiteBlockProbability,
      Nat.floor_div_eq_div] using hsource
  exact hsource'.trans <| pow_le_pow_left₀ (by positivity) hp.le _

/-- The closed block corridor is a measurable event. -/
theorem measurableSet_stableClosedBlockTube (ν : Measure ℝ) (α constant a width : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (stableClosedBlockTube ν α constant a width scale n) :=
  measurableSet_inHorizontalTube a (width * scale n) _

/-- The narrower open corridor is contained in the wider one with the same offset. This is the
monotonicity the two-sided bound of the theorem uses when comparing `f + ε`, `g - ε` with `f`, `g`. -/
theorem stableBlockTube_mono_width (ν : Measure ℝ) {α constant a w w' : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w)
    (hscale : 0 < scale n) :
    stableBlockTube ν α constant a w' scale n ⊆
      stableBlockTube ν α constant a w scale n := by
  have hscaled : w' * scale n < w * scale n :=
    mul_lt_mul_of_pos_right hww hscale
  have hlower : -a * (w * scale n) < -a * (w' * scale n) :=
    mul_lt_mul_of_neg_left hscaled (by linarith)
  have hupper : (1 - a) * (w' * scale n) < (1 - a) * (w * scale n) :=
    mul_lt_mul_of_pos_left hscaled (by linarith)
  intro increment h k
  have hk := h k
  exact ⟨hlower.trans hk.1, hk.2.trans hupper⟩

/-- Monotonicity of the block corridor probability in the corridor width. -/
theorem stableBlockCorridorProbability_mono_width (ν : Measure ℝ)
    {α constant a w w' : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hww : w' < w) (hscale : 0 < scale n) :
    stableBlockCorridorProbability ν α constant a w' scale n ≤
      stableBlockCorridorProbability ν α constant a w scale n :=
  measure_mono (stableBlockTube_mono_width ν ha0 ha1 hww hscale)

/-- Under an explicit Skorokhod `J₁` path-law limit for the normalized
stable-length blocks, the one-block corridor probability converges whenever
the limiting stable path gives zero mass to the corridor boundary.

The path-law hypothesis records the precise normalization used here:
`stableBlockLength α ν constant scale n` steps, each normalized by `scale n`.
It is the functional-limit input still missing from the stable random-walk
route; this theorem converts that input to the exact finite block event.
-/
theorem stableBlockCorridorProbability_tendsto_of_pathLawLimit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α constant a width : ℝ} {scale : ℕ → ℝ}
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P]
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop,
      0 < stableBlockLength α ν constant scale n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale
        (fun n => stableBlockLength α ν constant scale n))
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) P)
    (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width)
    (hboundary : P
      (frontier (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width))) = 0) :
    Tendsto (fun n => stableBlockCorridorProbability ν α constant a width scale n)
      atTop (nhds (P (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width)))) := by
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let corridor : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width)
  have hboundaryMap : P.map id (frontier corridor) = 0 := by
    simpa [corridor] using hboundary
  have hpathLaw := RandomWalk.tendsto_measure_normalizedStepBlockPathLaw_of_null_frontier
    (ν := ν) (spatialScale := scale) (blockLength := blockLength)
    P id hlimit hboundaryMap
  have heq : (fun n =>
      stableBlockCorridorProbability ν α constant a width scale n) =ᶠ[atTop]
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) := by
    filter_upwards [hblock, hscale] with n hblockn hscalen
    rw [stableBlockCorridorProbability, stableBlockTube]
    symm
    exact RandomWalk.normalizedStepBlockPathLaw_apply_horizontalOpenCorridor
      ν scale blockLength n hblockn hscalen ha haOne hwidth
  have hpathLaw' : Tendsto
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor)
      atTop (nhds (P corridor)) := by
    simpa [corridor] using hpathLaw
  exact hpathLaw'.congr' heq.symm

/-- The stable one-block corridor limit follows from the fixed-horizon
stable-domain input, path tightness, and slow variation of the norming factor.
The inverse-norming theorem identifies the limiting spatial scale as
`constant ^ (1 / α)` without requiring the slowly varying factor to converge. -/
theorem stableBlockCorridorProbability_tendsto_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α constant a width : ℝ} {normalization scale : ℕ → ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hα_le_two : α ≤ 2) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width)
    (hboundary : (P.map (Skorokhod.scalePath (constant ^ (1 / α))))
      (frontier (Skorokhod.rangeInOpenInterval
        (-(a * width)) ((1 - a) * width))) = 0) :
    Tendsto (fun n => stableBlockCorridorProbability ν α constant a width scale n)
      atTop (nhds ((P.map (Skorokhod.scalePath (constant ^ (1 / α))))
        (Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width)))) := by
  let block : ℕ → ℕ := fun n => stableBlockLength α ν constant scale n
  have hargumentEq (n : ℕ) : stableBlockArgument α ν constant scale n =
      constant * stableScaleTime α ν (scale n) := by
    rw [stableBlockArgument, stableScaleTime]
    ring
  have hblockEq : block = Asymptotics.floorBlockLength
      (fun n => constant * stableScaleTime α ν (scale n)) := by
    funext n
    simp [block, stableBlockLength, Asymptotics.floorBlockLength, hargumentEq n]
  have hscaleTimeTop : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα_le_two hslow
  have hargumentTop : Tendsto
      (fun n => constant * stableScaleTime α ν (scale n)) atTop atTop :=
    (hscaleTimeTop.comp hscale).const_mul_atTop hconstant
  have hblockTop : Tendsto block atTop atTop := by
    rw [hblockEq]
    exact Asymptotics.tendsto_floorBlockLength_atTop hargumentTop
  have hblockPos : ∀ᶠ n in atTop, 0 < block n := by
    simpa [block] using hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hnormPos : ∀ᶠ m in atTop, 0 < normalization m := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact hnorm.1 m hm
  have hnormBlock : ∀ᶠ n in atTop, 0 < normalization (block n) :=
    hblockTop.eventually hnormPos
  have hratio : Tendsto (fun n => normalization (block n) / scale n)
      atTop (nhds (constant ^ (1 / α))) := by
    rw [hblockEq]
    exact hnorm.tendsto_floorBlock_normalization_div_scale
      hα hα_le_two hslow hscale hconstant
  have hlimit :=
    ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hP htightBase hblockTop hscalePos hnormBlock hratio
  exact stableBlockCorridorProbability_tendsto_of_pathLawLimit
    (P := P.map (Skorokhod.scalePath (constant ^ (1 / α))))
    hscalePos hblockPos hlimit ha haOne hwidth hboundary

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable
