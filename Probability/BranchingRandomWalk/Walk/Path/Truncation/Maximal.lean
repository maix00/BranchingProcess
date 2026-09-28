import Probability.BranchingRandomWalk.Walk.Path.Block.Maximal.Fourth
import Probability.BranchingRandomWalk.Walk.Path.Block.Measurable
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Moment

/-!
# Maximal bounds for truncated increments

The fourth-power block maximal inequality is combined here with the moment
bounds for centered hard truncations.  All quantities on the right are
moments of the original increment law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- The fourth-moment numerator appearing in the maximal estimate for one
block of centered hard-truncated increments. -/
noncomputable def centeredTruncatedFourthNumerator
    (ν : Measure ℝ) (radius : ℝ) (length : ℕ) : ℝ :=
  ((length + 1 : ℕ) : ℝ) *
      (8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
        truncatedIncrementMean ν radius ^ 4)) +
    3 * (((length + 1 : ℕ) : ℝ) ^ 2) *
      (∫ x, x ^ 2 ∂ν) ^ 2

/-- The probability bound obtained from the fourth-moment numerator at a
positive oscillation threshold. -/
noncomputable def centeredTruncatedFourthBound
    (ν : Measure ℝ) (radius : ℝ) (length : ℕ) (threshold : ℝ) : ENNReal :=
  ENNReal.ofReal
    (centeredTruncatedFourthNumerator ν radius length / threshold ^ 4)

/-- A large block oscillation of the original path is caused either by a
discarded increment or by a large oscillation of the centered truncated path.
The extra deterministic margin is the accumulated truncation bias. -/
theorem exists_block_exists_abs_subset_largeIncrement_union_centeredTruncated
    (ν : Measure ℝ) {radius threshold : ℝ}
    (blocks length : ℕ) :
    {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} ⊆
      {path | ∃ i ∈ Finset.range (blocks * length + 1),
        radius < |path i|} ∪
      {path | ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold - ((length + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν radius| ≤
          |blockSum (j * length) (k + 1)
            (fun i => centeredTruncatedIncrement ν radius (path i))|} := by
  intro path hlarge
  by_cases htail : ∃ i ∈ Finset.range (blocks * length + 1),
      radius < |path i|
  · exact Or.inl htail
  · right
    obtain ⟨j, hj, k, hk, hklarge⟩ := hlarge
    refine ⟨j, hj, k, hk, ?_⟩
    let mean := truncatedIncrementMean ν radius
    let centeredPath : ℕ → ℝ :=
      fun i => centeredTruncatedIncrement ν radius (path i)
    have hcoordinate : ∀ i ∈ Finset.Ico (j * length) (j * length + (k + 1)),
        centeredPath i = path i - mean := by
      intro i hi
      have hklt : k < length + 1 := Finset.mem_range.1 hk
      have hkLe : k + 1 ≤ length + 1 :=
        Nat.succ_le_succ (Nat.lt_succ_iff.1 hklt)
      have hiUpper : i < blocks * length + 1 := by
        have hjSucc : j + 1 ≤ blocks := Nat.succ_le_iff.2 hj
        have hi' : i < j * length + (k + 1) := Finset.mem_Ico.1 hi |>.2
        calc
          i < j * length + (k + 1) := hi'
          _ ≤ j * length + (length + 1) := Nat.add_le_add_left hkLe _
          _ = (j + 1) * length + 1 := by
            rw [Nat.add_mul]
            omega
          _ ≤ blocks * length + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_right length hjSucc) 1
      have hnotLarge : ¬radius < |path i| := fun hiLarge =>
        htail ⟨i, Finset.mem_range.2 hiUpper, hiLarge⟩
      simp only [centeredPath, centeredTruncatedIncrement, mean]
      rw [truncatedIncrement_of_abs_le (le_of_not_gt hnotLarge)]
    have hblock : blockSum (j * length) (k + 1) centeredPath =
        blockSum (j * length) (k + 1) path - (k + 1) • mean := by
      calc
        blockSum (j * length) (k + 1) centeredPath =
            blockSum (j * length) (k + 1) (fun i => path i - mean) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoordinate i hi
        _ = _ := blockSum_sub_const (j * length) (k + 1) path mean
    have hreverse : blockSum (j * length) (k + 1) path =
        blockSum (j * length) (k + 1) centeredPath + (k + 1) • mean := by
      rw [hblock]
      abel
    have htriangle : |blockSum (j * length) (k + 1) path| ≤
        |blockSum (j * length) (k + 1) centeredPath| +
          ((k + 1 : ℕ) : ℝ) * |mean| := by
      rw [hreverse]
      refine (abs_add_le _ _).trans ?_
      rw [nsmul_eq_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)]
    have hkCast : (((k + 1 : ℕ) : ℝ)) ≤ ((length + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    have hbias : (((k + 1 : ℕ) : ℝ)) * |mean| ≤
        ((length + 1 : ℕ) : ℝ) * |mean| :=
      mul_le_mul_of_nonneg_right hkCast (abs_nonneg _)
    change threshold - ((length + 1 : ℕ) : ℝ) * |mean| ≤
      |blockSum (j * length) (k + 1) centeredPath|
    linarith

/-- Fourth-power maximal estimate for a block of centered hard-truncated IID
increments. -/
theorem maximal_ineq_pow_four_blockSum_centeredTruncated
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal (centeredTruncatedFourthNumerator ν radius n) := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmem4Source : MemLp f 4 ν :=
    memLp_centeredTruncatedIncrement_four ν hsq hradius
  have hmem4Map : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmem4Source
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement_of_integrable_sq
        ν hsq radius
  have hraw := maximal_ineq_pow_four_blockSum_iidSequenceLaw
    (ν.map f) hmem4Map hcenteredMap start ε n
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hfour : (∫ x, x ^ 4 ∂ν.map f) = ∫ x, f x ^ 4 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 4).aestronglyMeasurable
  have htwo : (∫ x, x ^ 2 ∂ν.map f) = ∫ x, f x ^ 2 ∂ν := by
    simpa using integral_map (μ := ν) (φ := f)
      hf.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable
  rw [hfour, htwo]
  have hfourLe :=
    integral_centeredTruncatedIncrement_pow_four_le_mean ν hsq hradius
  have htwoLe := integral_centeredTruncatedIncrement_sq_le ν hsq radius
  have hn : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  have htwoNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have htwoSq : (∫ x, f x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, x ^ 2 ∂ν) ^ 2 :=
    pow_le_pow_left₀ htwoNonneg htwoLe 2
  unfold centeredTruncatedFourthNumerator
  nlinarith

/-- Probability form of the centered-truncation fourth-power maximal bound. -/
theorem measure_exists_abs_blockSum_centeredTruncated_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) (n : ℕ) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |blockSum start (k + 1) path|} ≤
      centeredTruncatedFourthBound ν radius n threshold := by
  let ε : ℝ≥0 := ⟨threshold ^ 4, by positivity⟩
  have hmax := maximal_ineq_pow_four_blockSum_centeredTruncated
    ν hsq hradius start ε n
  have hevent : {path : ℕ → ℝ |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |blockSum start (k + 1) path|} =
      {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 4} := by
    ext path
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ blockSum start (k + 1) path ^ 4
      calc
        threshold ^ 4 ≤ |blockSum start (k + 1) path| ^ 4 :=
          pow_le_pow_left₀ hthreshold.le hkbound 4
        _ = blockSum start (k + 1) path ^ 4 := by
          calc
            |blockSum start (k + 1) path| ^ 4 =
                (|blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
            _ = (blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
            _ = blockSum start (k + 1) path ^ 4 := by ring
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ blockSum start (k + 1) path ^ 4 at hkbound
      have habsPow : |blockSum start (k + 1) path| ^ 4 =
          blockSum start (k + 1) path ^ 4 := by
        calc
          |blockSum start (k + 1) path| ^ 4 =
              (|blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
          _ = (blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
          _ = blockSum start (k + 1) path ^ 4 := by ring
      rw [← habsPow] at hkbound
      exact (pow_le_pow_iff_left₀ hthreshold.le (abs_nonneg _)
        (by norm_num : (4 : ℕ) ≠ 0)).1 hkbound
  rw [hevent]
  unfold centeredTruncatedFourthBound
  rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < threshold ^ 4)]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (by positivity : 0 < threshold ^ 4)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  rw [mul_comm]
  have hε : (ε : ENNReal) = ENNReal.ofReal (threshold ^ 4) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← hε]
  exact hmax

/-- Union bound for equal-length blocks of centered hard-truncated IID
increments.  The number of blocks is finite, while the underlying increment
path remains an infinite sequence. -/
theorem measure_exists_block_exists_abs_centeredTruncated_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} ≤
      (blocks : ℕ) * centeredTruncatedFourthBound ν radius length threshold := by
  let μ := iidSequenceLaw
    (ν.map (centeredTruncatedIncrement ν radius))
  let event (j : ℕ) : Set (ℕ → ℝ) := {path |
    ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |blockSum (j * length) (k + 1) path|}
  have hevent : {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} =
      ⋃ j ∈ Finset.range blocks, event j := by
    ext path
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, event]
    aesop
  rw [hevent]
  calc
    μ (⋃ j ∈ Finset.range blocks, event j) ≤
        ∑ j ∈ Finset.range blocks, μ (event j) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range blocks,
        centeredTruncatedFourthBound ν radius length threshold := by
      apply Finset.sum_le_sum
      intro j hj
      exact measure_exists_abs_blockSum_centeredTruncated_ge_le
        ν hsq hradius (j * length) hthreshold length
    _ = (blocks : ℕ) *
        centeredTruncatedFourthBound ν radius length threshold := by
      simp

/-- The same multiblock estimate on the original canonical sample space,
with centered truncation applied coordinatewise. -/
theorem measure_exists_block_exists_abs_map_centeredTruncated_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1)
          (fun i => centeredTruncatedIncrement ν radius (path i))|} ≤
      (blocks : ℕ) * centeredTruncatedFourthBound ν radius length threshold := by
  let f := centeredTruncatedIncrement ν radius
  let mapPath : (ℕ → ℝ) → (ℕ → ℝ) := fun path i => f (path i)
  let event : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |blockSum (j * length) (k + 1) path|}
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmapPath : Measurable mapPath :=
    Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have hevent : MeasurableSet event :=
    measurableSet_exists_block_exists_abs_blockSum_ge
      blocks length threshold
  have hmapLaw : (iidSequenceLaw ν).map mapPath =
      iidSequenceLaw (ν.map f) := by
    simpa [mapPath] using iidSequenceLaw_map_coordinatewise ν f hf
  have hmeasure : (iidSequenceLaw ν) (mapPath ⁻¹' event) =
      iidSequenceLaw (ν.map f) event := by
    rw [← hmapLaw, Measure.map_apply hmapPath hevent]
  change (iidSequenceLaw ν) (mapPath ⁻¹' event) ≤ _
  rw [hmeasure]
  exact measure_exists_block_exists_abs_centeredTruncated_ge_le
    ν hsq hradius blocks length hthreshold

/-- Global equal-block oscillation estimate for the original IID increment
path.  The first term pays for discarded increments and the second term is
the fourth-moment estimate for the centered truncation. -/
theorem measure_exists_block_exists_abs_ge_le_of_truncation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ) {threshold : ℝ}
    (hgap : ((length + 1 : ℕ) : ℝ) *
        |truncatedIncrementMean ν radius| < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * centeredTruncatedFourthBound ν radius length
          (threshold - ((length + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν radius|) := by
  let originalLarge : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |blockSum (j * length) (k + 1) path|}
  let discarded : Set (ℕ → ℝ) := {path |
    ∃ i ∈ Finset.range (blocks * length + 1), radius < |path i|}
  let centeredLarge : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold - ((length + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν radius| ≤
        |blockSum (j * length) (k + 1)
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
      (blocks : ℕ) * centeredTruncatedFourthBound ν radius length
        (threshold - ((length + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν radius|) := by
    exact measure_exists_block_exists_abs_map_centeredTruncated_ge_le
      ν hsq hradius blocks length (sub_pos.2 hgap)
  change (iidSequenceLaw ν) originalLarge ≤ _
  calc
    (iidSequenceLaw ν) originalLarge ≤
        (iidSequenceLaw ν) (discarded ∪ centeredLarge) :=
      measure_mono hsubset
    _ ≤ (iidSequenceLaw ν) discarded +
        (iidSequenceLaw ν) centeredLarge := measure_union_le _ _
    _ ≤ _ := add_le_add hdiscarded hcentered

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
