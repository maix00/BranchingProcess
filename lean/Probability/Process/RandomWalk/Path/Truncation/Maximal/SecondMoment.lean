/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated
public import Probability.Process.RandomWalk.Path.Truncation.Maximal

/-!
# Second-moment maximal bounds for truncated walks

Bounded centered truncations have finite second moments even when the original
increment law has infinite variance.  This file turns that fact into a
multiblock large-deviation estimate with an explicit discarded-tail term.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The second moment of a hard-truncated increment is exactly the truncated
second moment of the original law. -/
theorem integral_truncatedIncrement_sq_eq_truncatedSecondMoment
    (ν : Measure ℝ) (radius : ℝ) :
    (∫ x, truncatedIncrement radius x ^ 2 ∂ν) =
      truncatedSecondMoment ν radius := by
  have hfun : (fun x : ℝ => truncatedIncrement radius x ^ 2) =
      (Set.Icc (-radius) radius).indicator (fun x => x ^ 2) := by
    funext x
    by_cases hx : |x| ≤ radius
    · have hmem : x ∈ Set.Icc (-radius) radius := abs_le.mp hx
      simp [truncatedIncrement_of_abs_le hx, Set.indicator_of_mem hmem]
    · have hmem : x ∉ Set.Icc (-radius) radius := by
        intro hmem
        exact hx (abs_le.mpr hmem)
      simp [truncatedIncrement_of_lt_abs (lt_of_not_ge hx), Set.indicator_of_notMem hmem]
  rw [hfun, truncatedSecondMoment, integral_indicator measurableSet_Icc]

/-- The second-moment probability bound for a block of centered truncated
increments. -/
noncomputable def truncatedCenteredSecondBound
    (ν : Measure ℝ) (radius : ℝ) (length : ℕ) (threshold : ℝ) : ENNReal :=
  ENNReal.ofReal (((length + 1 : ℕ) : ℝ) *
    truncatedSecondMoment ν radius / threshold ^ 2)

/-- Squared maximal inequality for the centered hard-truncated IID sequence.
No second moment assumption is made on the original law. -/
theorem maximal_ineq_sq_blockSum_centeredTruncated_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ}
    (start : ℕ) (ε : ℝ≥0) (length : ℕ) :
    ε * (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      (ε : ℝ) ≤
        (Finset.range (length + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal (((length + 1 : ℕ) : ℝ) * truncatedSecondMoment ν radius) := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmemSource : MemLp f 2 ν :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
      (integrable_centeredTruncatedIncrement_pow ν radius 2)
  have hmemMap : MemLp id 2 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmemSource
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement ν radius
  have hmax := maximal_ineq_sq_blockSum_iidSequenceLaw
    (ν.map f) hmemMap hcenteredMap start ε length
  have hvariance : variance id (ν.map f) ≤ truncatedSecondMoment ν radius := by
    rw [variance_id_map hf.aemeasurable]
    calc
      variance f ν ≤ ∫ x, f x ^ 2 ∂ν :=
        variance_le_expectation_sq hf.aestronglyMeasurable
      _ ≤ ∫ x, truncatedIncrement radius x ^ 2 ∂ν :=
        integral_centeredTruncatedIncrement_sq_le_truncated ν radius
      _ = truncatedSecondMoment ν radius :=
        integral_truncatedIncrement_sq_eq_truncatedSecondMoment ν radius
  refine hmax.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 ≤ (((length + 1 : ℕ) : ℝ)) := by positivity
  exact mul_le_mul_of_nonneg_left hvariance hlen

/-- The probability that a centered-truncated block ever exceeds a positive
absolute threshold is controlled by its truncated second moment. -/
theorem measure_exists_abs_blockSum_centeredTruncated_ge_le_second
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ}
    (start : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) (length : ℕ) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} ≤
      truncatedCenteredSecondBound ν radius length threshold := by
  let ε : ℝ≥0 := ⟨threshold ^ 2, by positivity⟩
  have hmax := maximal_ineq_sq_blockSum_centeredTruncated_bounded
    (radius := radius) ν start ε length
  have hevent : {path : ℕ → ℝ |
      ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} =
      {path | (ε : ℝ) ≤
        (Finset.range (length + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} := by
    ext path
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 2 ≤ AdditivePath.blockSum start (k + 1) path ^ 2
      calc
        threshold ^ 2 ≤ |AdditivePath.blockSum start (k + 1) path| ^ 2 :=
          pow_le_pow_left₀ hthreshold.le hkbound 2
        _ = AdditivePath.blockSum start (k + 1) path ^ 2 := sq_abs _
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 2 ≤ AdditivePath.blockSum start (k + 1) path ^ 2 at hkbound
      have hsquares : |threshold| ^ 2 ≤
          |AdditivePath.blockSum start (k + 1) path| ^ 2 := by
        rw [← sq_abs threshold, ← sq_abs (AdditivePath.blockSum start (k + 1) path)] at hkbound
        exact hkbound
      have habs : |threshold| ≤ |AdditivePath.blockSum start (k + 1) path| :=
        (sq_le_sq₀ (abs_nonneg threshold) (abs_nonneg _)).1 hsquares
      rwa [abs_of_pos hthreshold] at habs
  rw [hevent]
  unfold truncatedCenteredSecondBound
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < threshold ^ 2)]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (by positivity : 0 < threshold ^ 2)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  rw [mul_comm]
  have hε : (ε : ENNReal) = ENNReal.ofReal (threshold ^ 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← hε]
  exact hmax

/-- A finite union of equal-length centered-truncated blocks obeys the sum of
the second-moment bounds for each block. -/
theorem measure_exists_block_exists_abs_centeredTruncated_ge_le_second
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ}
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      (blocks : ℕ) * truncatedCenteredSecondBound ν radius length threshold := by
  let μ := iidSequenceLaw (ν.map (centeredTruncatedIncrement ν radius))
  let event (j : ℕ) : Set (ℕ → ℝ) := {path |
    ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|}
  have hevent : {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} =
      ⋃ j ∈ Finset.range blocks, event j := by
    ext path
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, event]
    aesop
  rw [hevent]
  calc
    μ (⋃ j ∈ Finset.range blocks, event j) ≤
        ∑ j ∈ Finset.range blocks, μ (event j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range blocks,
        truncatedCenteredSecondBound ν radius length threshold := by
      apply Finset.sum_le_sum
      intro j hj
      exact measure_exists_abs_blockSum_centeredTruncated_ge_le_second
        ν (j * length) hthreshold length
    _ = (blocks : ℕ) * truncatedCenteredSecondBound ν radius length threshold := by simp

/-- Coordinatewise centered truncation transfers the multiblock estimate to
the original IID sample space. -/
theorem measure_exists_block_exists_abs_map_centeredTruncated_ge_le_second
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ}
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1)
          (fun i => centeredTruncatedIncrement ν radius (path i))|} ≤
      (blocks : ℕ) * truncatedCenteredSecondBound ν radius length threshold := by
  let f := centeredTruncatedIncrement ν radius
  let mapPath : (ℕ → ℝ) → (ℕ → ℝ) := fun path i => f (path i)
  let event : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|}
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmapPath : Measurable mapPath :=
    Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have hevent : MeasurableSet event :=
    measurableSet_exists_block_exists_abs_blockSum_ge blocks length threshold
  have hmapLaw : (iidSequenceLaw ν).map mapPath =
      iidSequenceLaw (ν.map f) := by
    simpa [mapPath] using iidSequenceLaw_map_coordinatewise ν f hf
  have hmeasure : (iidSequenceLaw ν) (mapPath ⁻¹' event) =
      iidSequenceLaw (ν.map f) event := by
    rw [← hmapLaw, Measure.map_apply hmapPath hevent]
  change (iidSequenceLaw ν) (mapPath ⁻¹' event) ≤ _
  rw [hmeasure]
  exact measure_exists_block_exists_abs_centeredTruncated_ge_le_second
    ν blocks length hthreshold

/-- An infinite-variance truncation estimate for the original IID walk.  Large
block oscillation is paid for either by a discarded increment or by the
second-moment bound for the centered truncated block. -/
theorem measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius threshold : ℝ}
    (blocks length : ℕ)
    (hgap : ((length + 1 : ℕ) : ℝ) *
        |truncatedIncrementMean ν radius| < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * truncatedCenteredSecondBound ν radius length
          (threshold - ((length + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν radius|) := by
  let originalLarge : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|}
  let discarded : Set (ℕ → ℝ) := {path |
    ∃ i ∈ Finset.range (blocks * length + 1), radius < |path i|}
  let centeredLarge : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold - ((length + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν radius| ≤
        |AdditivePath.blockSum (j * length) (k + 1)
          (fun i => centeredTruncatedIncrement ν radius (path i))|}
  have hsubset : originalLarge ⊆ discarded ∪ centeredLarge :=
    exists_block_exists_abs_subset_largeIncrement_union_centeredTruncated
      ν blocks length
  have hdiscarded : (iidSequenceLaw ν) discarded ≤
      (blocks * length + 1 : ℕ) * ν {x | radius < |x|} := by
    exact iidSequenceLaw_measure_exists_mem_le ν
      {x | radius < |x|}
      (measurableSet_lt measurable_const continuous_abs.measurable)
      (blocks * length + 1)
  have hcentered : (iidSequenceLaw ν) centeredLarge ≤
      (blocks : ℕ) * truncatedCenteredSecondBound ν radius length
        (threshold - ((length + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν radius|) := by
    exact measure_exists_block_exists_abs_map_centeredTruncated_ge_le_second
      ν blocks length (sub_pos.2 hgap)
  change (iidSequenceLaw ν) originalLarge ≤ _
  calc
    (iidSequenceLaw ν) originalLarge ≤
        (iidSequenceLaw ν) (discarded ∪ centeredLarge) := measure_mono hsubset
    _ ≤ (iidSequenceLaw ν) discarded +
        (iidSequenceLaw ν) centeredLarge := measure_union_le _ _
    _ ≤ _ := add_le_add hdiscarded hcentered

end ProbabilityTheory.RandomWalk

end
