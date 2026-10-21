/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.EndpointBandTransfer.Rate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Core
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Stable lower bounds for shifted endpoint-return blocks

This combines the stable escape rate, the variable-block path limit, and
open-set Portmanteau for an arbitrary shifted interval. It supplies the
finite endpoint-band probabilities needed by the discrete return kernel.

The public interfaces in `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete`
are:

- `eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit`:
  if $p$ is below the limiting path-law mass of each open endpoint band,
  then eventually
  $p\leq\operatorname{Law}_\nu(\mathrm{endpointBandReturnBlockEvent}
  (l s_n,u s_n,\varepsilon s_n,i,m_n))$ for every $i\in[-3,3]$.
- `eventually_endpointCorridorBlockProbability_ge_of_stablePathLimit`:
  if $p$ is below the limiting mass of one open corridor event, then
  eventually $p\leq\operatorname{Law}_\nu(\mathrm{endpointCorridorBlockEvent}
  (l s_n,u s_n,l_e s_n,u_e s_n,m_n))$.
- `eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio`:
  for any block sequence with $|I_n|/T_n\to a^\alpha$, the same eventual
  endpoint-band lower bound from the first bullet holds.
- `eventually_endpointCorridorBlockProbability_ge_of_stableScaleTimeRatio`:
  under the same time-ratio hypothesis, the corridor probability bound from
  the second bullet holds for any fixed open endpoint corridor.
- `eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio`:
  for a finite index set $I$, the corridor bound holds eventually for every
  $i\in I$, with the corridor and endpoint interval allowed to depend on $i$.

The balanced stable partition asymptotics used by the cell proof are placed
in `Lower/Lemmas/BalancedBlocks.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A stable path-law limit transfers a common lower mass for finitely many
shifted open endpoint corridors to discrete IID return-band events. This
interface is independent of how the block-length sequence was selected. -/
theorem eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {lower upper epsilon : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map Z
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower + 4 * epsilon) (upper - 4 * epsilon)
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
            (epsilon * scale n) i (blockLength n)) :=
  eventually_forall_normalizedEndpointBandReturnProbability_ge_of_pathLawLimit
    ν scale blockLength Z hlimit hscale hblock hlower hupper lowerBound hbelow

/-- Open-set Portmanteau transfers one arbitrary open displacement window,
not only a band centered at one of the seven return indices. -/
theorem eventually_endpointCorridorBlockProbability_ge_of_stablePathLimit
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop Z (fun _ => iidSequenceLaw ν) P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (lowerBound : ENNReal)
    (hbelow : lowerBound < P.map Z
      (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper)) :
    ∀ᶠ n : ℕ in atTop,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n)) := by
  let corridor := Skorokhod.rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper
  have hport := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    lower upper endpointLower endpointUpper
  have hbelow' : lowerBound < P.map Z corridor := by simpa [corridor] using hbelow
  have hstrict : lowerBound < atTop.liminf
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    hbelow'.trans_le (by
      simpa [corridor, RandomWalk.normalizedStepBlockPathLaw] using hport)
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have heventuallyPath := eventually_lt_of_lt_liminf hstrict hbounded
  have hsetEq : ∀ᶠ n in atTop,
      {increment : ℕ → ℝ |
        InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
              (Fin.last (blockLength n)) / scale n ∈
            Set.Ioo endpointLower endpointUpper} =
        endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n) := by
    filter_upwards [hscale] with n hs
    ext increment
    change
      (InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) / scale n ∈
          Set.Ioo endpointLower endpointUpper) ↔
      (InOpenPartialSumCorridor (lower * scale n) (upper * scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) ∈
          Set.Ioo (endpointLower * scale n) (endpointUpper * scale n))
    constructor
    · rintro ⟨hpath, hend⟩
      refine ⟨hpath, ?_⟩
      constructor
      · exact (lt_div_iff₀ hs).mp hend.1
      · exact (div_lt_iff₀ hs).mp hend.2
    · rintro ⟨hpath, hend⟩
      refine ⟨hpath, ?_⟩
      constructor
      · exact (lt_div_iff₀ hs).mpr hend.1
      · exact (div_lt_iff₀ hs).mpr hend.2
  have hpathLawEq : ∀ᶠ n in atTop,
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n corridor =
        iidSequenceLaw ν
          (endpointCorridorBlockEvent
            (lower * scale n) (upper * scale n)
            (endpointLower * scale n) (endpointUpper * scale n)
            (blockLength n)) := by
    filter_upwards [hblock, hscale, hsetEq] with n hn hs hset
    rw [RandomWalk.normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
      ν scale blockLength n hn hs hlower hupper]
    simpa [corridor] using congrArg (iidSequenceLaw ν) hset
  filter_upwards [heventuallyPath, hpathLawEq] with n hpath heq
  rw [heq] at hpath
  exact hpath.le

/-- The endpoint-band lower estimate holds for any block-length sequence
whose stable time ratio tends to the prescribed amplitude. This avoids
requiring the block length to be a particular floor, which is essential when
partitioning a cell into blocks of exactly equal or nearly equal length. -/
theorem eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {lower upper epsilon : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower + 4 * epsilon) (upper - 4 * epsilon)
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
            (epsilon * scale n) i (blockLength n)) := by
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hnormRatio' :=
    hscale.stableNorming.tendsto_normalization_div_scale_of_blockLengthRatio
      hα hα₂ hslow hscaleTop
      (Real.rpow_pos_of_pos hamplitude α) hblockTop hblockRatio
  have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
    rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
    have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (nhds amplitude) := by
    convert hnormRatio' using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  exact eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
    ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
    hscalePos (hblockTop.eventually (eventually_gt_atTop 0)) hlower hupper
    lowerBound hbelow

/-- The variable-block stable limit transfers a fixed arbitrary endpoint
window inside a shifted corridor whenever the block's stable time ratio has a
positive limit. This is the one-block bridge estimate for distinct endpoint
cores. -/
theorem eventually_endpointCorridorBlockProbability_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (lowerBound : ENNReal)
    (hbelow : lowerBound < P.map (Skorokhod.scalePath amplitude)
      (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper)) :
    ∀ᶠ n : ℕ in atTop,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBlockEvent
          (lower * scale n) (upper * scale n)
          (endpointLower * scale n) (endpointUpper * scale n)
          (blockLength n)) := by
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hnormRatio' :=
    hscale.stableNorming.tendsto_normalization_div_scale_of_blockLengthRatio
      hα hα₂ hslow hscaleTop
      (Real.rpow_pos_of_pos hamplitude α) hblockTop hblockRatio
  have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
    rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
    have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (nhds amplitude) := by
    convert hnormRatio' using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  exact eventually_endpointCorridorBlockProbability_ge_of_stablePathLimit
    ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
    hscalePos (hblockTop.eventually (eventually_gt_atTop 0))
    hlower hupper lowerBound hbelow

/-- One stable path limit transfers a uniform lower mass for a finite family
of open endpoint windows. This is the form needed for bridges between
different endpoint cores. -/
theorem eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (blockLength : ℕ → ℕ)
    (hblockTop : Tendsto blockLength atTop atTop)
    {amplitude : ℝ} (hamplitude : 0 < amplitude)
    (hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) /
        stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)))
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (lower upper endpointLower endpointUpper : ι → ℝ)
    (hlower : ∀ i ∈ indices, lower i < 0)
    (hupper : ∀ i ∈ indices, 0 < upper i)
    (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ indices,
      lowerBound < P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn
          (lower i) (upper i) (endpointLower i) (endpointUpper i))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ indices,
        lowerBound ≤ iidSequenceLaw ν
          (endpointCorridorBlockEvent
            (lower i * scale n) (upper i * scale n)
            (endpointLower i * scale n) (endpointUpper i * scale n)
            (blockLength n)) := by
  classical
  apply indices.eventually_all.2
  intro i hi
  exact eventually_endpointCorridorBlockProbability_ge_of_stableScaleTimeRatio
    hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
    hamplitude hblockRatio (hlower i hi) (hupper i hi) lowerBound
    (hbelow i hi)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

end
