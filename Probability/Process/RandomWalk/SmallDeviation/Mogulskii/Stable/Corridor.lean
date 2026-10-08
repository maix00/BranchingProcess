/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Distributions.Stable.Attraction.Norming.Inverse
public import Probability.Sequence.IID
public import Probability.Process.Stable.EscapeRate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal

/-!
# One-block corridors for the stable Mogulskii route

The one-block step of Mogulskii's stable proof estimates the probability that the increment path stays in a
corridor of normalized width `w` over a block of `stableBlockLength α ν constant a n` steps, which is
`a n ^ α / L* (a n)` steps up to the constant factor `constant`. The small-deviation scale
`n * L* (a n) / a n ^ α` is what turns a per-block constant into the corridor rate of the theorem.

For `α < 2` the limit process has jumps, so the estimate has to go through the stable Lévy process and the
Skorokhod `J₁` topology; the killed-interval spectral expansion used for the Gaussian case is not available
here and is not used. At `α = 2` the slowly varying factor is the truncated second moment, and the block
length reduces to the diffusive block length with the constant rescaled by that moment, which is the link
by which the Gaussian specialization reuses the diffusive estimates.

The one-block estimate is conditional on the block path-law limit: the last
theorem transfers an explicit `J₁` limit to the corridor probability when the
limiting path law gives zero mass to the corridor boundary.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii



/-! ## The block length at `α = 2` -/

/-- At `α = 2` the slowly varying factor of (3) is the truncated second moment, so the stable block length
is the floor of `constant * scale n ^ 2` divided by that moment. -/
@[simp] theorem stableBlockLength_two (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockLength 2 ν constant scale n =
      ⌊constant * scale n ^ 2 / truncatedSecondMoment ν (scale n)⌋₊ := by
  simp [stableBlockLength, stableBlockArgument, stableSlowVariation_two]

/-- At `α = 2`, if the truncated second moment at the scale is the constant `c`, the stable block length is
the diffusive block length with the constant rescaled by `c`. This is the link by which the Gaussian
specialization reuses the diffusive estimates. -/
theorem stableBlockLength_two_of_truncatedSecondMoment_eq (ν : Measure ℝ) {constant c : ℝ}
    {scale : ℕ → ℝ} {n : ℕ} (hc : truncatedSecondMoment ν (scale n) = c) :
    stableBlockLength 2 ν constant scale n = diffusiveBlockLength (constant / c) scale n := by
  rw [stableBlockLength_two, hc, diffusiveBlockLength, div_mul_eq_mul_div]

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

/-- A strict source block-oscillation event implies the closed range bound
for the corresponding normalized càdlàg block path. -/
theorem blockOscillationLTEvent_subset_normalizedStepBlockRangeOscillation
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hscale : 0 < scale n) (width : ℝ) :
    {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
      (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)} ⊆
    {increment | RandomWalk.normalizedStepBlockCadlagPathIcc
        scale blockLength n increment ∈ Skorokhod.rangeOscillationLe width} := by
  intro increment hosc
  change ∀ i j : Fin (blockLength n + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) j| <
        width * scale n at hosc
  intro s t
  obtain ⟨i, hi⟩ :=
    RandomWalk.exists_normalizedStepCadlagPathIcc_eq_scaledDisplacement
      (fun _ => scale n) (blockLength n) increment s
  obtain ⟨j, hj⟩ :=
    RandomWalk.exists_normalizedStepCadlagPathIcc_eq_scaledDisplacement
      (fun _ => scale n) (blockLength n) increment t
  have hpartialI :
      Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) i =
        AdditivePath.displacement (i : ℕ) increment := by
    rw [RandomWalk.partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
  have hpartialJ :
      Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) j =
        AdditivePath.displacement (j : ℕ) increment := by
    rw [RandomWalk.partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
  have hraw : |AdditivePath.displacement (i : ℕ) increment -
      AdditivePath.displacement (j : ℕ) increment| < width * scale n := by
    simpa [hpartialI, hpartialJ] using hosc i j
  have hnormalized :
      |(scale n)⁻¹ * AdditivePath.displacement (i : ℕ) increment -
        (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment| =
        |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| / scale n := by
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hscale), div_eq_mul_inv]
    ring
  change |RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale n)
      (blockLength n) increment s -
    RandomWalk.normalizedStepCadlagPathIcc (fun _ => scale n)
      (blockLength n) increment t| ≤ width
  rw [hi, hj, hnormalized]
  exact (div_lt_iff₀ hscale).2 (by simpa [mul_comm] using hraw) |>.le

/-- The finite source block-oscillation probability is bounded above by the
closed range-oscillation probability of its càdlàg step-path image. This is
the event bridge needed to combine the source's independent-block inequality
with the stable path-law upper transfer. -/
theorem iidSequenceLaw_measure_blockOscillationLT_le_normalizedStepBlockPathLaw
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hscale : 0 < scale n) (width : ℝ) :
    iidSequenceLaw ν
        {increment | blockOscillationLTEvent (width * scale n) (blockLength n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)} ≤
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n
        (Skorokhod.rangeOscillationLe width) := by
  have hmeas : Measurable
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength n) := by
    change Measurable (RandomWalk.normalizedStepCadlagPathIcc
      (fun _ => scale n) (blockLength n))
    exact RandomWalk.measurable_normalizedStepCadlagPathIcc
      (fun _ => scale n) (blockLength n)
  rw [RandomWalk.normalizedStepBlockPathLaw, Measure.map_apply hmeas
    (Skorokhod.isClosed_rangeOscillationLe width).measurableSet]
  apply measure_mono
  exact blockOscillationLTEvent_subset_normalizedStepBlockRangeOscillation
    scale blockLength n hscale width

/-- The closed range-oscillation event of a fixed-parameter variable block
is bounded by a slightly wider stable-process range tube under the block-path
`J₁` limit. The margin handles the closed boundary without a null-boundary
assumption, and the range-diameter event preserves the sharp Mogulskii
constant. -/
theorem limsup_normalizedStepBlockRangeOscillation_le_stableProcessTube
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    (hc : 0 < c) (hwidth : 0 ≤ width) (hmargin : 0 < margin) :
    atTop.limsup (fun n =>
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n
        (Skorokhod.rangeOscillationLe width)) ≤
      P (stableProcessTube ((width + margin) / (2 * c))) := by
  have hport : atTop.limsup (fun n =>
      RandomWalk.normalizedStepBlockPathLaw ν scale blockLength n
        (Skorokhod.rangeOscillationLe width)) ≤
      (P.map (Skorokhod.scalePath c)) (Skorokhod.rangeOscillationLe width) := by
    simpa [RandomWalk.normalizedStepBlockPathLaw, Measure.map_id] using
      hlimit.limsup_measure_map_le_of_isClosed
        (Skorokhod.isClosed_rangeOscillationLe width)
  have hclosedBound :
      (P.map (Skorokhod.scalePath c)) (Skorokhod.rangeOscillationLe width) ≤
        P (stableProcessTube ((width + margin) / (2 * c))) := by
    have hscaleMeas : Measurable (fun path : CadlagPath unitInterval ℝ =>
        Skorokhod.scalePath c path) := by
      exact (Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)).measurable
    rw [Measure.map_apply hscaleMeas
      (Skorokhod.isClosed_rangeOscillationLe width).measurableSet]
    apply measure_mono_ae
    filter_upwards [hP.ae_start_eq_zero] with path hstart
    intro hpath
    change Skorokhod.OscillationBounded
      (Skorokhod.scalePath c path) width at hpath
    have hosc : path ∈ Skorokhod.rangeOscillationLe (width / c) := by
      intro s t
      have hscaled := hpath s t
      have hmul : c * |path s - path t| ≤ width := by
        have heq : |c * path s - c * path t| =
            c * |path s - path t| := by
          rw [← mul_sub, abs_mul, abs_of_pos hc]
        rw [Skorokhod.scalePath_apply, Skorokhod.scalePath_apply] at hscaled
        rw [← heq]
        exact hscaled
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
    have hopen := Skorokhod.rangeOscillationLe_subset_oscillationInOpenTube
      (width / c) (margin / c) (div_pos hmargin hc) hosc
    have hwidthEq : width / c + margin / c =
        2 * ((width + margin) / (2 * c)) := by
      field_simp [hc.ne']
    have hopen' : path ∈ Skorokhod.oscillationInOpenTube
        (2 * ((width + margin) / (2 * c))) := by
      rw [← hwidthEq]
      exact hopen
    change path ∈ {f | f ⊥ = 0} ∩ Skorokhod.oscillationInOpenTube
      (2 * ((width + margin) / (2 * c)))
    exact ⟨hstart, hopen'⟩
  exact hport.trans hclosedBound

/-- The one-block probability in Mogul'skii's discrete Lemma 3(c) is bounded
in the limit by the slightly wider stable-process range tube. This combines
the exact finite-block event bridge with closed-set Portmanteau. -/
theorem limsup_iidSequenceLaw_blockOscillationLT_le_stableProcessTube
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) (P.map (Skorokhod.scalePath c)))
    (hc : 0 < c) (hwidth : 0 ≤ width) (hmargin : 0 < margin) :
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
  have hstable := limsup_normalizedStepBlockRangeOscillation_le_stableProcessTube
    hP hlimit hc hwidth hmargin
  change atTop.limsup finiteBlockProbability ≤ _
  exact hlimsup.trans hstable

/-- The source's independent-block inequality and the fixed-parameter stable
path limit give an eventual exponential upper bound for an open horizontal
tube. The one-block base may be any strict upper bound on the slightly wider
stable range-tube probability. -/
theorem eventually_openHorizontalTubeProbability_le_pow_of_blockPathLimit
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    {α c width margin : ℝ} {scale : ℕ → ℝ} {horizon blockLength : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
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
    hP hscale hlimit hc hwidth.le hmargin
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
    openHorizontalTubeProbability_le_pow_blockOscillationLT_source
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
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
