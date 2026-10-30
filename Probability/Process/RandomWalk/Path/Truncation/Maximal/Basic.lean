/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Maximal.Fourth
public import Probability.Process.RandomWalk.Path.Block.Measurable
public import Probability.Process.RandomWalk.Path.Truncation.Moment

import all Probability.Process.RandomWalk.Path.Truncation.Maximal.Lemmas.Truncation

/-!
# Maximal bounds for truncated increments

Write $\widehat x_R=\operatorname{truncatedIncrement}(R,x)$ and
$m_R=\int \widehat x_R\,d\nu=\operatorname{truncatedIncrementMean}(\nu,R)$;
then $\operatorname{centeredTruncatedIncrement}(\nu,R,x)=\widehat x_R-m_R$.
For an increment path $x$, write $S_{s,k}(x)=\operatorname{blockSum}_x(s,k+1)$
and $S_{j,k}^{(n)}(x)=S_{jn,k}(x)$.

## Public declarations

* `centeredTruncatedFourthNumerator ν R n` is
  $(n+1)\bigl(8(R^2\int x^2\,d\nu+m_R^4)\bigr)
  +3(n+1)^2(\int x^2\,d\nu)^2$.
* `centeredTruncatedFourthBound ν R n t` is the fourth-moment bound
  $\operatorname{ofReal}(N_c/t^4)$ formed from that numerator.
* `truncatedCenteredFourthNumerator ν R n` is the same expression with
  $\int x^2\,d\nu$ replaced by $\int \widehat x_R^2\,d\nu$.
* `truncatedCenteredFourthBound ν R n t` is the corresponding
  $\operatorname{ofReal}(N_R/t^4)$ bound.
* `maximal_ineq_pow_four_blockSum_centeredTruncated` and
  `maximal_ineq_pow_four_blockSum_centeredTruncated_bounded` give fourth-power
  maximal inequalities
  $\varepsilon\,\mathbb P(\varepsilon\le
  \max_{0\le k\le n}|S_{start,k}|^4)
  \le \operatorname{ofReal}(N_c)$ and its bounded-truncation counterpart for
  the centered truncated IID walk; the first assumes a finite second moment
  of $\nu$, while the second uses only that $\nu$ is a probability measure.
* `measure_exists_abs_blockSum_centeredTruncated_ge_le` and
  `measure_exists_abs_blockSum_centeredTruncated_ge_le_bounded` bound a
  one-block event by
  $\mathbb P(\exists k\le n:\ t\le|S_{start,k}|)\le
  \operatorname{ofReal}(N_c/t^4)$, with the corresponding bound for bounded
  truncation.
* `measure_exists_block_exists_abs_centeredTruncated_ge_le` and
  `measure_exists_block_exists_abs_centeredTruncated_ge_le_bounded` give the
  bound
  $\mathbb P(\exists j<q,\exists k\le n:\ t\le|S_{j,k}^{(n)}|)
  \le q\,\operatorname{ofReal}(N_c/t^4)$ over `blocks` equal-length blocks
  for the centered truncated walk. The declarations
  `measure_exists_block_exists_abs_map_centeredTruncated_ge_le` and
  `measure_exists_block_exists_abs_map_centeredTruncated_ge_le_bounded` state
  the same bounds on the original IID sample space after applying truncation
  coordinatewise.
* `measure_exists_block_exists_abs_ge_le_of_truncation` and
  `measure_exists_block_exists_abs_ge_le_of_truncation_bounded` bound the
  original-walk block-oscillation probability by
  $(q n+1)\,\nu\{|x|>R\}+
  q\,\operatorname{ofReal}(N_c/(t-(n+1)|m_R|)^4)$ when
  $(n+1)|m_R|<t$; the first assumes $\int x^2\,d\nu<\infty$, while the
  second assumes only that $\nu$ is a probability measure.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk


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

/-- Fourth-moment numerator for the centered truncated walk.  Every term is
finite for a probability law, even when the original increment has infinite
variance. -/
noncomputable def truncatedCenteredFourthNumerator
    (ν : Measure ℝ) (radius : ℝ) (length : ℕ) : ℝ :=
  ((length + 1 : ℕ) : ℝ) *
      (8 * (radius ^ 2 * ∫ x, truncatedIncrement radius x ^ 2 ∂ν +
        truncatedIncrementMean ν radius ^ 4)) +
    3 * (((length + 1 : ℕ) : ℝ) ^ 2) *
      (∫ x, truncatedIncrement radius x ^ 2 ∂ν) ^ 2

/-- Fourth-moment maximal probability bound for hard-truncated increments;
it only requires that the increment law be a probability measure. -/
noncomputable def truncatedCenteredFourthBound
    (ν : Measure ℝ) (radius : ℝ) (length : ℕ) (threshold : ℝ) : ENNReal :=
  ENNReal.ofReal
    (truncatedCenteredFourthNumerator ν radius length / threshold ^ 4)

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
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal (centeredTruncatedFourthNumerator ν radius n) := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmem4Source : MemLp f 4 ν :=
    memLp_centeredTruncatedIncrement_four ν radius
  have hmem4Map : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmem4Source
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement ν radius
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
  have hfourLe := integral_centeredTruncatedIncrement_pow_four_le ν hradius
  have htruncSqLe : ∫ x, truncatedIncrement radius x ^ 2 ∂ν ≤
      ∫ x, x ^ 2 ∂ν := by
    exact integral_mono (integrable_truncatedIncrement_pow ν radius 2) hsq
      fun x => by
        rw [← sq_abs (truncatedIncrement radius x), ← sq_abs x]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncatedIncrement_le_abs radius x) 2
  have hfourLeOriginal :
      ∫ x, f x ^ 4 ∂ν ≤
        8 * (radius ^ 2 * ∫ x, x ^ 2 ∂ν +
          truncatedIncrementMean ν radius ^ 4) := by
    refine hfourLe.trans ?_
    gcongr
  have htwoLe := integral_centeredTruncatedIncrement_sq_le ν hsq radius
  have hn : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  have htwoNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have htwoSq : (∫ x, f x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, x ^ 2 ∂ν) ^ 2 :=
    pow_le_pow_left₀ htwoNonneg htwoLe 2
  unfold centeredTruncatedFourthNumerator
  nlinarith

/-- Fourth-power maximal estimate for centered hard-truncated increments with
no moment assumption on the original law. -/
theorem maximal_ineq_pow_four_blockSum_centeredTruncated_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal (truncatedCenteredFourthNumerator ν radius n) := by
  let f := centeredTruncatedIncrement ν radius
  have hf : Measurable f := measurable_centeredTruncatedIncrement ν radius
  have hmem4Source : MemLp f 4 ν := memLp_centeredTruncatedIncrement_four ν radius
  have hmem4Map : MemLp id 4 (ν.map f) := by
    rw [memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
      hf.aemeasurable]
    simpa [Function.comp_def, id] using hmem4Source
  have hcenteredMap : ∫ x, x ∂ν.map f = 0 := by
    calc
      (∫ x, x ∂ν.map f) = ∫ x, f x ∂ν := by
        simpa using integral_map (μ := ν) (φ := f)
          hf.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := integral_centeredTruncatedIncrement ν radius
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
  have hfourLe := integral_centeredTruncatedIncrement_pow_four_le ν hradius
  have htwoLe := integral_centeredTruncatedIncrement_sq_le_truncated ν radius
  have htwoNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have htruncNonneg : 0 ≤ ∫ x, truncatedIncrement radius x ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  have htwoSq : (∫ x, f x ^ 2 ∂ν) ^ 2 ≤
      (∫ x, truncatedIncrement radius x ^ 2 ∂ν) ^ 2 :=
    pow_le_pow_left₀ htwoNonneg htwoLe 2
  unfold truncatedCenteredFourthNumerator
  nlinarith

/-- Probability form of the infinite-variance truncation maximal bound. -/
theorem measure_exists_abs_blockSum_centeredTruncated_ge_le_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) (n : ℕ) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} ≤
      truncatedCenteredFourthBound ν radius n threshold := by
  let ε : ℝ≥0 := ⟨threshold ^ 4, by positivity⟩
  have hmax := maximal_ineq_pow_four_blockSum_centeredTruncated_bounded
    ν hradius start ε n
  have hevent : {path : ℕ → ℝ |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} =
      {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 4} := by
    ext path
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ AdditivePath.blockSum start (k + 1) path ^ 4
      calc
        threshold ^ 4 ≤ |AdditivePath.blockSum start (k + 1) path| ^ 4 :=
          pow_le_pow_left₀ hthreshold.le hkbound 4
        _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by
          calc
            |AdditivePath.blockSum start (k + 1) path| ^ 4 =
                (|AdditivePath.blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
            _ = (AdditivePath.blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
            _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by ring
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ AdditivePath.blockSum start (k + 1) path ^ 4 at hkbound
      have habsPow : |AdditivePath.blockSum start (k + 1) path| ^ 4 =
          AdditivePath.blockSum start (k + 1) path ^ 4 := by
        calc
          |AdditivePath.blockSum start (k + 1) path| ^ 4 =
              (|AdditivePath.blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
          _ = (AdditivePath.blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
          _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by ring
      rw [← habsPow] at hkbound
      exact (pow_le_pow_iff_left₀ hthreshold.le (abs_nonneg _)
        (by norm_num : (4 : ℕ) ≠ 0)).1 hkbound
  rw [hevent]
  unfold truncatedCenteredFourthBound
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

/-- Probability form of the centered-truncation fourth-power maximal bound. -/
theorem measure_exists_abs_blockSum_centeredTruncated_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (start : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) (n : ℕ) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} ≤
      centeredTruncatedFourthBound ν radius n threshold := by
  let ε : ℝ≥0 := ⟨threshold ^ 4, by positivity⟩
  have hmax := maximal_ineq_pow_four_blockSum_centeredTruncated
    ν hsq hradius start ε n
  have hevent : {path : ℕ → ℝ |
      ∃ k ∈ Finset.range (n + 1),
        threshold ≤ |AdditivePath.blockSum start (k + 1) path|} =
      {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 4} := by
    ext path
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ AdditivePath.blockSum start (k + 1) path ^ 4
      calc
        threshold ^ 4 ≤ |AdditivePath.blockSum start (k + 1) path| ^ 4 :=
          pow_le_pow_left₀ hthreshold.le hkbound 4
        _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by
          calc
            |AdditivePath.blockSum start (k + 1) path| ^ 4 =
                (|AdditivePath.blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
            _ = (AdditivePath.blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
            _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by ring
    · rintro ⟨k, hk, hkbound⟩
      refine ⟨k, hk, ?_⟩
      change threshold ^ 4 ≤ AdditivePath.blockSum start (k + 1) path ^ 4 at hkbound
      have habsPow : |AdditivePath.blockSum start (k + 1) path| ^ 4 =
          AdditivePath.blockSum start (k + 1) path ^ 4 := by
        calc
          |AdditivePath.blockSum start (k + 1) path| ^ 4 =
              (|AdditivePath.blockSum start (k + 1) path| ^ 2) ^ 2 := by ring
          _ = (AdditivePath.blockSum start (k + 1) path ^ 2) ^ 2 := by rw [sq_abs]
          _ = AdditivePath.blockSum start (k + 1) path ^ 4 := by ring
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
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      (blocks : ℕ) * centeredTruncatedFourthBound ν radius length threshold := by
  let μ := iidSequenceLaw
    (ν.map (centeredTruncatedIncrement ν radius))
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
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1)
          (fun i => centeredTruncatedIncrement ν radius (path i))|} ≤
      (blocks : ℕ) * centeredTruncatedFourthBound ν radius length threshold := by
  let f := centeredTruncatedIncrement ν radius
  let mapPath : (ℕ → ℝ) → (ℕ → ℝ) := fun path i => f (path i)
  let event : Set (ℕ → ℝ) := {path |
    ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
      threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|}
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

/-- Union bound for finite equal-length blocks under hard truncation, without
any moment assumption on the original increment law. -/
theorem measure_exists_block_exists_abs_centeredTruncated_ge_le_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw
        (ν.map (centeredTruncatedIncrement ν radius))) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      (blocks : ℕ) * truncatedCenteredFourthBound ν radius length threshold := by
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
        truncatedCenteredFourthBound ν radius length threshold := by
      apply Finset.sum_le_sum
      intro j hj
      exact measure_exists_abs_blockSum_centeredTruncated_ge_le_bounded
        ν hradius (j * length) hthreshold length
    _ = (blocks : ℕ) * truncatedCenteredFourthBound ν radius length threshold := by simp

/-- The bounded-truncation multiblock estimate on the original IID sample
space, with the centered truncation applied coordinatewise. -/
theorem measure_exists_block_exists_abs_map_centeredTruncated_ge_le_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1)
          (fun i => centeredTruncatedIncrement ν radius (path i))|} ≤
      (blocks : ℕ) * truncatedCenteredFourthBound ν radius length threshold := by
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
  exact measure_exists_block_exists_abs_centeredTruncated_ge_le_bounded
    ν hradius blocks length hthreshold

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
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * centeredTruncatedFourthBound ν radius length
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

/-- Global multiblock oscillation estimate from hard truncation, valid for
probability laws with infinite variance. -/
theorem measure_exists_block_exists_abs_ge_le_of_truncation_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius threshold : ℝ} (hradius : 0 ≤ radius)
    (blocks length : ℕ)
    (hgap : ((length + 1 : ℕ) : ℝ) *
        |truncatedIncrementMean ν radius| < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * truncatedCenteredFourthBound ν radius length
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
      (blocks : ℕ) * truncatedCenteredFourthBound ν radius length
        (threshold - ((length + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν radius|) := by
    exact measure_exists_block_exists_abs_map_centeredTruncated_ge_le_bounded
      ν hradius blocks length (sub_pos.2 hgap)
  change (iidSequenceLaw ν) originalLarge ≤ _
  calc
    (iidSequenceLaw ν) originalLarge ≤
        (iidSequenceLaw ν) (discarded ∪ centeredLarge) := measure_mono hsubset
    _ ≤ (iidSequenceLaw ν) discarded +
        (iidSequenceLaw ν) centeredLarge := measure_union_le _ _
    _ ≤ _ := add_le_add hdiscarded hcentered

end ProbabilityTheory.RandomWalk
