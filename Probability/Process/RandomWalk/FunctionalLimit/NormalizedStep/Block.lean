/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Basic
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Functional limits for variable-length random-walk blocks

This module separates the number of steps in a block from the spatial
normalization indexed by the outer limit parameter. It identifies open and
closed path corridors with the corresponding finite horizontal-tube events,
then applies Portmanteau to any stated path-law limit.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The càdlàg step path for a block whose length and spatial normalization
may both depend on an outer parameter. -/
noncomputable def normalizedStepBlockCadlagPathIcc
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) :
    ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ :=
  fun n => normalizedStepCadlagPathIcc (fun _ => spatialScale n) (blockLength n)

/-- The law of a variable-length normalized block path under i.i.d.
increments. -/
noncomputable def normalizedStepBlockPathLaw (ν : Measure ℝ)
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ) :
    Measure (CadlagPath unitInterval ℝ) :=
  (iidSequenceLaw ν).map (normalizedStepBlockCadlagPathIcc spatialScale blockLength n)

noncomputable instance normalizedStepBlockPathLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ) :
    IsProbabilityMeasure (normalizedStepBlockPathLaw ν spatialScale blockLength n) := by
  unfold normalizedStepBlockPathLaw
  infer_instance

/-- Membership of a variable-length normalized step path in an open
Skorokhod corridor is equivalent to the corresponding strict finite grid
inequalities in the original coordinates. -/
theorem normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) {n : ℕ}
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (increment : ℕ → ℝ) :
    normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInOpenInterval lower upper ↔
      ∀ k : Fin (blockLength n),
        lower * spatialScale n < AdditivePath.displacement (k + 1) increment ∧
          AdditivePath.displacement (k + 1) increment < upper * spatialScale n := by
  change normalizedStepCadlagPathIcc (fun _ => spatialScale n) (blockLength n) increment ∈
      Skorokhod.rangeInOpenInterval lower upper ↔ _
  rw [normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
    (fun _ => spatialScale n) hblock hlower hupper]
  constructor
  · intro h k
    have hk := h k
    dsimp only [InOpenCorridorOnGrid] at hk
    rw [normalizedStepPath_grid (fun _ => spatialScale n) hblock,
      inv_mul_eq_div] at hk
    exact ⟨(lt_div_iff₀ hscale).mp hk.1,
      (div_lt_iff₀ hscale).mp hk.2⟩
  · intro h k
    dsimp only [InOpenCorridorOnGrid]
    rw [normalizedStepPath_grid (fun _ => spatialScale n) hblock,
      inv_mul_eq_div]
    exact ⟨(lt_div_iff₀ hscale).mpr (h k).1,
      (div_lt_iff₀ hscale).mpr (h k).2⟩

/-- A fixed normalized open horizontal corridor of width `width` is the
Skorokhod corridor with boundaries `-a * width` and `(1-a) * width`. -/
theorem normalizedStepBlockCadlagPathIcc_mem_horizontalOpenCorridor_iff
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) {n : ℕ}
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {a width : ℝ} (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width)
    (increment : ℕ → ℝ) :
    normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width) ↔
      InOpenHorizontalTube a (width * spatialScale n) (blockLength n) increment := by
  rw [normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
    spatialScale blockLength hblock hscale
    (neg_lt_zero.mpr (mul_pos ha hwidth))
    (mul_pos (sub_pos.mpr haOne) hwidth)]
  constructor
  · intro h k
    have hk := h k
    change -(a * width) * spatialScale n <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        ((1 - a) * width) * spatialScale n at hk
    change -a * (width * spatialScale n) <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        (1 - a) * (width * spatialScale n)
    simpa [mul_assoc] using hk
  · intro h k
    have hk := h k
    change -a * (width * spatialScale n) <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        (1 - a) * (width * spatialScale n) at hk
    change -(a * width) * spatialScale n <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        ((1 - a) * width) * spatialScale n
    simpa [mul_assoc] using hk

/-- Membership of a variable-length normalized step path in a centered
open corridor with an open terminal interval is exactly a strict finite tube
together with the normalized endpoint constraint. -/
theorem normalizedStepBlockCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) {n : ℕ}
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width)
    (increment : ℕ → ℝ) :
    normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper ↔
      InOpenHorizontalTube (1 / 2) (width * spatialScale n)
          (blockLength n) increment ∧
        AdditivePath.displacement (blockLength n) increment / spatialScale n ∈
          Set.Ioo endpointLower endpointUpper := by
  change normalizedStepCadlagPathIcc (fun _ => spatialScale n)
      (blockLength n) increment ∈ _ ↔ _
  exact normalizedStepCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
    (fun _ => spatialScale n) hblock hscale hwidth increment

/-- Membership of a variable-length normalized step path in a closed
Skorokhod corridor is equivalent to the corresponding weak finite grid
inequalities in the original coordinates. -/
theorem normalizedStepBlockCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) {n : ℕ}
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {lower upper : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInClosedInterval lower upper ↔
      ∀ k : Fin (blockLength n),
        lower * spatialScale n ≤ AdditivePath.displacement (k + 1) increment ∧
          AdditivePath.displacement (k + 1) increment ≤ upper * spatialScale n := by
  change normalizedStepCadlagPathIcc (fun _ => spatialScale n) (blockLength n) increment ∈
      Skorokhod.rangeInClosedInterval lower upper ↔ _
  rw [normalizedStepCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
    (fun _ => spatialScale n) hblock hlower hupper]
  constructor
  · intro h k
    have hk := h k
    dsimp only [InClosedCorridorOnGrid] at hk
    rw [normalizedStepPath_grid (fun _ => spatialScale n) hblock,
      inv_mul_eq_div] at hk
    exact ⟨(le_div_iff₀ hscale).mp hk.1,
      (div_le_iff₀ hscale).mp hk.2⟩
  · intro h k
    dsimp only [InClosedCorridorOnGrid]
    rw [normalizedStepPath_grid (fun _ => spatialScale n) hblock,
      inv_mul_eq_div]
    exact ⟨(le_div_iff₀ hscale).mpr (h k).1,
      (div_le_iff₀ hscale).mpr (h k).2⟩

/-- A fixed normalized closed horizontal corridor of width `width` is the
Skorokhod corridor with boundaries `-a * width` and `(1-a) * width`. -/
theorem normalizedStepBlockCadlagPathIcc_mem_horizontalClosedCorridor_iff
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) {n : ℕ}
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {a width : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hwidth : 0 ≤ width)
    (increment : ℕ → ℝ) :
    normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width) ↔
      InHorizontalTube a (width * spatialScale n) (blockLength n) increment := by
  rw [normalizedStepBlockCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
    spatialScale blockLength hblock hscale
    (neg_nonpos.mpr (mul_nonneg ha hwidth))
    (mul_nonneg (sub_nonneg.mpr haOne) hwidth)]
  constructor
  · intro h k
    have hk := h k
    change -(a * width) * spatialScale n ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        ((1 - a) * width) * spatialScale n at hk
    change -a * (width * spatialScale n) ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        (1 - a) * (width * spatialScale n)
    simpa [mul_assoc] using hk
  · intro h k
    have hk := h k
    change -a * (width * spatialScale n) ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        (1 - a) * (width * spatialScale n) at hk
    change -(a * width) * spatialScale n ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        ((1 - a) * width) * spatialScale n
    simpa [mul_assoc] using hk

/-- The path-law probability of an open normalized block corridor is the
i.i.d. probability of its finite horizontal-tube event. -/
theorem normalizedStepBlockPathLaw_apply_horizontalOpenCorridor
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {a width : ℝ} (ha : 0 < a) (haOne : a < 1) (hwidth : 0 < width) :
    normalizedStepBlockPathLaw ν spatialScale blockLength n
        (Skorokhod.rangeInOpenInterval (-(a * width)) ((1 - a) * width)) =
      iidSequenceLaw ν
        {increment | InOpenHorizontalTube a (width * spatialScale n)
          (blockLength n) increment} := by
  rw [normalizedStepBlockPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepBlockCadlagPathIcc_mem_horizontalOpenCorridor_iff
      spatialScale blockLength hblock hscale ha haOne hwidth increment
  · exact measurable_normalizedStepCadlagPathIcc
      (fun _ => spatialScale n) (blockLength n)
  · exact Skorokhod.measurableSet_rangeInOpenInterval
      (-(a * width)) ((1 - a) * width)

/-- The path-law probability of a closed normalized block corridor is the
i.i.d. probability of its finite horizontal-tube event. -/
theorem normalizedStepBlockPathLaw_apply_horizontalClosedCorridor
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {a width : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hwidth : 0 ≤ width) :
    normalizedStepBlockPathLaw ν spatialScale blockLength n
        (Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width)) =
      iidSequenceLaw ν
        {increment | InHorizontalTube a (width * spatialScale n)
          (blockLength n) increment} := by
  rw [normalizedStepBlockPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepBlockCadlagPathIcc_mem_horizontalClosedCorridor_iff
      spatialScale blockLength hblock hscale ha haOne hwidth increment
  · exact measurable_normalizedStepCadlagPathIcc
      (fun _ => spatialScale n) (blockLength n)
  · exact Skorokhod.measurableSet_rangeInClosedInterval
      (-(a * width)) ((1 - a) * width)

/-- The path-law probability of a centered open block corridor with an open
endpoint constraint is the i.i.d. probability of the corresponding finite
tube and normalized endpoint event. -/
theorem normalizedStepBlockPathLaw_apply_centeredOpenIntervalEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    normalizedStepBlockPathLaw ν spatialScale blockLength n
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) =
      iidSequenceLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (width * spatialScale n)
            (blockLength n) increment ∧
          AdditivePath.displacement (blockLength n) increment / spatialScale n ∈
            Set.Ioo endpointLower endpointUpper} := by
  rw [normalizedStepBlockPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    exact normalizedStepBlockCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
      spatialScale blockLength hblock hscale hwidth increment
  · exact measurable_normalizedStepCadlagPathIcc
      (fun _ => spatialScale n) (blockLength n)
  · exact Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
      (-(width / 2)) (width / 2) endpointLower endpointUpper

/-- The path-law probability of an arbitrary shifted open block corridor
with an open endpoint window is the IID probability of its finite
partial-sum event. -/
theorem normalizedStepBlockPathLaw_apply_shiftedCorridorEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (spatialScale : ℕ → ℝ) (blockLength : ℕ → ℕ) (n : ℕ)
    (hblock : 0 < blockLength n) (hscale : 0 < spatialScale n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) :
    normalizedStepBlockPathLaw ν spatialScale blockLength n
        (Skorokhod.rangeInOpenIntervalEndsIn
          lower upper endpointLower endpointUpper) =
      iidSequenceLaw ν {increment : ℕ → ℝ |
        InOpenPartialSumCorridor (lower * spatialScale n) (upper * spatialScale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) ∧
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
            (Fin.last (blockLength n)) / spatialScale n ∈
          Set.Ioo endpointLower endpointUpper} := by
  rw [normalizedStepBlockPathLaw, Measure.map_apply]
  · congr 1
    ext increment
    change normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ∈
        Skorokhod.rangeInOpenIntervalEndsIn lower upper endpointLower endpointUpper ↔ _
    rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
    constructor
    · rintro ⟨hgrid, hend⟩
      have hcorridor : InOpenPartialSumCorridor
          (lower * spatialScale n) (upper * spatialScale n)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment) := by
        apply (inOpenPartialSumCorridor_iff_succ
          (mul_neg_of_neg_of_pos hlower hscale)
          (mul_pos hupper hscale)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)).2
        intro k
        have hk := (normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
          spatialScale blockLength hblock hscale hlower hupper increment).1 hgrid k
        have hsum := partialSum_blockCoordinates 0 increment k.succ
        have hsum' :
            Fin.partialSum
                (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
                k.succ = AdditivePath.displacement (k + 1) increment := by
          rw [hsum, AdditivePath.blockSum_eq_displacement_natAdd]
          simp
        rw [hsum']
        exact hk
      have hlast :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
              (Fin.last (blockLength n)) =
            AdditivePath.displacement (blockLength n) increment := by
        rw [partialSum_blockCoordinates,
          AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      refine ⟨hcorridor, ?_⟩
      change endpointLower <
          normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ⊤ ∧
        normalizedStepBlockCadlagPathIcc spatialScale blockLength n increment ⊤ <
          endpointUpper at hend
      simpa [normalizedStepBlockCadlagPathIcc,
        normalizedStepCadlagPathIcc_apply, normalizedStepPath_one,
        hlast, div_eq_mul_inv, mul_comm] using hend
    · rintro ⟨hcell, hend⟩
      have hgrid : ∀ k : Fin (blockLength n),
          lower * spatialScale n < AdditivePath.displacement (k + 1) increment ∧
            AdditivePath.displacement (k + 1) increment < upper * spatialScale n := by
        intro k
        have hk := (inOpenPartialSumCorridor_iff_succ
          (mul_neg_of_neg_of_pos hlower hscale)
          (mul_pos hupper hscale)
          (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)).1
            hcell k
        have hsum := partialSum_blockCoordinates 0 increment k.succ
        have hsum' :
            Fin.partialSum
                (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
                k.succ = AdditivePath.displacement (k + 1) increment := by
          rw [hsum, AdditivePath.blockSum_eq_displacement_natAdd]
          simp
        rw [hsum'] at hk
        exact hk
      have hlast :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment)
              (Fin.last (blockLength n)) =
            AdditivePath.displacement (blockLength n) increment := by
        rw [partialSum_blockCoordinates,
          AdditivePath.blockSum_eq_displacement_natAdd]
        simp
      refine ⟨?_, ?_⟩
      · exact (normalizedStepBlockCadlagPathIcc_mem_rangeInOpenInterval_iff_grid
          spatialScale blockLength hblock hscale hlower hupper increment).2 hgrid
      · simpa [normalizedStepBlockCadlagPathIcc,
          normalizedStepCadlagPathIcc_apply, normalizedStepPath_one,
          hlast, div_eq_mul_inv, mul_comm] using hend
  · exact measurable_normalizedStepCadlagPathIcc
      (fun _ => spatialScale n) (blockLength n)
  · exact Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper

/-- The closed-set Portmanteau bound for a variable-length normalized block
transfers to the corresponding finite horizontal-tube probability. No
boundary-null assumption is needed for this one-sided upper bound. -/
theorem limsup_horizontalTubeProbability_le_of_normalizedStepBlockPathLimit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {spatialScale : ℕ → ℝ} {blockLength : ℕ → ℕ}
    (hscale : ∀ᶠ n in atTop, 0 < spatialScale n)
    (hblock : ∀ᶠ n in atTop, 0 < blockLength n)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hlimit : TendstoInDistribution
      (normalizedStepBlockCadlagPathIcc spatialScale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν) P)
    {a width : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hwidth : 0 ≤ width) :
    atTop.limsup (fun n => horizontalTubeProbability (iidSequenceLaw ν)
      a (width * spatialScale n) (blockLength n)) ≤
      P (Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width)) := by
  have hcorridor : atTop.limsup (fun n =>
      normalizedStepBlockPathLaw ν spatialScale blockLength n
        (Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width))) ≤
      P (Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width)) := by
    simpa [normalizedStepBlockPathLaw, Measure.map_id] using
      hlimit.limsup_measure_skorokhodCorridor_le
        (-(a * width)) ((1 - a) * width)
  refine Eq.trans_le ?_ hcorridor
  apply limsup_congr
  filter_upwards [hblock, hscale] with n hn hs
  change iidSequenceLaw ν
      {increment | InHorizontalTube a (width * spatialScale n)
        (blockLength n) increment} =
    normalizedStepBlockPathLaw ν spatialScale blockLength n
      (Skorokhod.rangeInClosedInterval (-(a * width)) ((1 - a) * width))
  symm
  exact normalizedStepBlockPathLaw_apply_horizontalClosedCorridor
    ν spatialScale blockLength n hn hs ha haOne hwidth

/-- A stated path-law limit transfers probabilities of any fixed measurable
event whose boundary has zero limiting mass. -/
theorem tendsto_measure_normalizedStepBlockPathLaw_of_null_frontier
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {spatialScale : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (normalizedStepBlockCadlagPathIcc spatialScale blockLength)
      atTop limit (fun _ => iidSequenceLaw ν) P)
    {event : Set (CadlagPath unitInterval ℝ)}
    (hboundary : P.map limit (frontier event) = 0) :
    Tendsto (fun n => normalizedStepBlockPathLaw ν spatialScale blockLength n event)
      atTop (nhds (P.map limit event)) := by
  exact hlimit.tendsto_measure_map_of_null_frontier hboundary

end ProbabilityTheory.RandomWalk

end
