/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.FirstCrossing
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Two ordered excursions in a finite window

The event below is a discrete modulus event: two increments of the partial-sum
path, in time order and within one finite window, both exceed a fixed size. A
first-crossing argument reduces it to a crossing followed by a fresh
excursion. This is the probabilistic core of the IID local-oscillation bound.

## Public declarations

* `twoOrderedPrefixExcursions length threshold` and
  `twoOrderedBlockExcursions start length threshold` define two chronologically
  ordered partial-sum increments, each of absolute size at least `threshold`,
  in a finite prefix or a shifted block.
* `measurableSet_twoOrderedPrefixExcursions` and
  `measurableSet_twoOrderedBlockExcursions` establish measurability of these
  events.
* `measure_twoOrderedBlockExcursions_translate_eq` identifies the shifted
  block probability with the initial-block probability under IID increments.
* `measure_twoOrderedPrefixExcursions_le_sq_of_blockBound` bounds the
  probability of two ordered increments of size at least `2 * threshold` by
  the square of the one-block prefix-exceedance bound at `threshold`.

The event is
`\(\{x\mid\exists i\le j\le k\le l\le L,\
|S_j-S_i|\ge r\land|S_l-S_k|\ge r\}\)`;
the probability bound applies with `\(r=2\,threshold\)`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk



/-- Two ordered oscillations of the partial-sum path, with both endpoint
pairs contained in the first `length` increments. -/
def twoOrderedPrefixExcursions (length : ℕ) (threshold : ℝ) : Set (ℕ → ℝ) :=
  {path | ∃ i j k l : ℕ,
    i ≤ j ∧ j ≤ k ∧ k ≤ l ∧ l ≤ length ∧
      threshold ≤ |AdditivePath.displacement j path -
        AdditivePath.displacement i path| ∧
      threshold ≤ |AdditivePath.displacement l path -
        AdditivePath.displacement k path|}

private lemma abs_sub_le_sum_abs (x y : ℝ) :
    |x - y| ≤ |x| + |y| := by
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [le_abs_self x, neg_le_abs x,
    le_abs_self y, neg_le_abs y]

private lemma split_abs_sub_le {threshold x y : ℝ}
    (hlarge : 2 * threshold ≤ |x - y|) :
    threshold ≤ |x| ∨ threshold ≤ |y| := by
  by_contra h
  push Not at h
  have htriangle := abs_sub_le_sum_abs x y
  linarith

private lemma twoOrderedPrefixExcursions_subset_firstCrossing
    (length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    twoOrderedPrefixExcursions length (2 * threshold) ⊆
      blockPrefixExceedance 0 length threshold ∩
        blockPrefixExceedanceAfter (firstPrefixExceedanceTime threshold)
          length threshold := by
  intro path hevent
  rcases hevent with ⟨i, j, k, l, hij, hjk, hkl, hl,
    hfirstExc, hsecondExc⟩
  let τ := firstPrefixExceedanceTime threshold
  have hfirstSplit := split_abs_sub_le hfirstExc
  have hfirstAt : threshold ≤ |AdditivePath.displacement i path| ∨
      threshold ≤ |AdditivePath.displacement j path| := by
    rcases hfirstSplit with hj | hi
    · exact Or.inr (by simpa [AdditivePath.displacement_zero] using hj)
    · exact Or.inl (by simpa [AdditivePath.displacement_zero] using hi)
  have hfirstBlock : path ∈ blockPrefixExceedance 0 length threshold := by
    rcases hfirstAt with hi | hj
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := 0) (finish := i) (length := length) hthreshold
        (by omega) (by omega) (by simpa using hi)
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := 0) (finish := j) (length := length) hthreshold
        (by omega) (by omega) (by simpa using hj)
  have hτle : τ path ≤ j := by
    apply (firstPrefixExceedanceTime_le_iff_blockPrefixExceedance
      threshold hthreshold j path).2
    rcases hfirstAt with hi | hj
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := 0) (finish := i) (length := j) hthreshold
        (by omega) (by omega) (by simpa using hi)
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := 0) (finish := j) (length := j) hthreshold
        (by omega) (by omega) (by simpa using hj)
  have hτnotTop : τ path ≠ ⊤ := by
    intro htop
    rw [htop] at hτle
    simp at hτle
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hτnotTop
  have hτeq : τ path = r := hr.symm
  have hrj : r ≤ j := by
    have hle : (r : WithTop ℕ) ≤ j := by simpa [hτeq] using hτle
    exact WithTop.coe_le_coe.mp hle
  have hsecondIdentity :
      (AdditivePath.displacement l path - AdditivePath.displacement r path) -
        (AdditivePath.displacement k path - AdditivePath.displacement r path) =
          AdditivePath.displacement l path - AdditivePath.displacement k path := by
    ring
  have hsecondRecentered : 2 * threshold ≤
      |(AdditivePath.displacement l path - AdditivePath.displacement r path) -
        (AdditivePath.displacement k path - AdditivePath.displacement r path)| := by
    rw [hsecondIdentity]
    exact hsecondExc
  have hsecondAt := split_abs_sub_le hsecondRecentered
  have hfuture : path ∈ blockPrefixExceedance r length threshold := by
    rcases hsecondAt with hl' | hk'
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := r) (finish := l) (length := length) hthreshold
        (by omega) (by omega) (by simpa using hl')
    · exact blockPrefixExceedance_of_displacementDifference path
        (start := r) (finish := k) (length := length) hthreshold
        (by omega) (by omega) (by simpa using hk')
  refine ⟨hfirstBlock, ?_⟩
  simp only [blockPrefixExceedanceAfter, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  exact ⟨r, hτeq, hfuture⟩

/-- The two-excursion event is measurable because it depends on finitely many
partial-sum coordinates. -/
theorem measurableSet_twoOrderedPrefixExcursions
    (length : ℕ) (threshold : ℝ) :
    MeasurableSet (twoOrderedPrefixExcursions length threshold) := by
  classical
  rw [show twoOrderedPrefixExcursions length threshold =
    ⋃ i : ℕ, ⋃ j : ℕ, ⋃ k : ℕ, ⋃ l : ℕ,
      {path : ℕ → ℝ |
        i ≤ j ∧ j ≤ k ∧ k ≤ l ∧ l ≤ length ∧
          threshold ≤ |AdditivePath.displacement j path -
            AdditivePath.displacement i path| ∧
          threshold ≤ |AdditivePath.displacement l path -
            AdditivePath.displacement k path|} by
    ext path
    simp [twoOrderedPrefixExcursions]]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => ?_
  by_cases hindex : i ≤ j ∧ j ≤ k ∧ k ≤ l ∧ l ≤ length
  · have hfirst := measurableSet_le
        (measurable_const : Measurable fun _ : ℕ → ℝ => threshold)
        (continuous_abs.measurable.comp
          ((displacement_measurable (E := ℝ) j).sub
            (displacement_measurable (E := ℝ) i)))
    have hsecond := measurableSet_le
        (measurable_const : Measurable fun _ : ℕ → ℝ => threshold)
        (continuous_abs.measurable.comp
          ((displacement_measurable (E := ℝ) l).sub
            (displacement_measurable (E := ℝ) k)))
    have hfirst' : MeasurableSet
        {path : ℕ → ℝ | threshold ≤
          |AdditivePath.displacement j path - AdditivePath.displacement i path|} :=
      hfirst.congr (by ext path; rfl)
    have hsecond' : MeasurableSet
        {path : ℕ → ℝ | threshold ≤
          |AdditivePath.displacement l path - AdditivePath.displacement k path|} :=
      hsecond.congr (by ext path; rfl)
    simpa only [hindex, true_and, Set.ofPred_and] using hfirst'.inter hsecond'
  · have hempty :
      {path : ℕ → ℝ |
          i ≤ j ∧ j ≤ k ∧ k ≤ l ∧ l ≤ length ∧
            threshold ≤ |AdditivePath.displacement j path -
              AdditivePath.displacement i path| ∧
            threshold ≤ |AdditivePath.displacement l path -
              AdditivePath.displacement k path|} = ∅ := by
      ext path
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hindex ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [hempty]
    exact MeasurableSet.empty

/-- Two ordered excursions within a block beginning at the deterministic
increment index `start`. -/
def twoOrderedBlockExcursions (start length : ℕ) (threshold : ℝ) :
    Set (ℕ → ℝ) :=
  (fun path : ℕ → ℝ => fun k => path (start + k)) ⁻¹'
    twoOrderedPrefixExcursions length threshold

theorem measurableSet_twoOrderedBlockExcursions
    (start length : ℕ) (threshold : ℝ) :
    MeasurableSet (twoOrderedBlockExcursions start length threshold) :=
  (measurableSet_twoOrderedPrefixExcursions length threshold).preimage
    (measurable_natAdd start)

/-- The two-excursion event in a deterministic block has the same probability
as in an initial block under the canonical IID increment law. -/
theorem measure_twoOrderedBlockExcursions_translate_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (threshold : ℝ) :
    iidSequenceLaw ν (twoOrderedBlockExcursions start length threshold) =
      iidSequenceLaw ν (twoOrderedPrefixExcursions length threshold) := by
  have hshift : Measurable
      (fun path : ℕ → ℝ => fun k => path (start + k)) := measurable_natAdd start
  calc
    _ = (iidSequenceLaw ν).map
        (fun path : ℕ → ℝ => fun k => path (start + k))
          (twoOrderedPrefixExcursions length threshold) := by
      rw [twoOrderedBlockExcursions, Measure.map_apply hshift
        (measurableSet_twoOrderedPrefixExcursions length threshold)]
    _ = _ := by rw [iidSequenceLaw_map_natAdd]

/-- For an IID increment sequence, two ordered excursions in a finite window
are bounded by the square of the one-window excursion probability. The
factorization is at the first crossing of the first oscillation threshold. -/
theorem measure_twoOrderedPrefixExcursions_le_sq_of_blockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (length : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold)
    (bound : ENNReal)
    (hbound : iidSequenceLaw ν
      (blockPrefixExceedance 0 length threshold) ≤ bound) :
    iidSequenceLaw ν (twoOrderedPrefixExcursions length (2 * threshold)) ≤
      bound ^ 2 := by
  calc
    _ ≤ iidSequenceLaw ν
        (blockPrefixExceedance 0 length threshold ∩
          blockPrefixExceedanceAfter (firstPrefixExceedanceTime threshold)
            length threshold) :=
      measure_mono (twoOrderedPrefixExcursions_subset_firstCrossing
        length hthreshold)
    _ = iidSequenceLaw ν (blockPrefixExceedance 0 length threshold) ^ 2 := by
      rw [measure_firstPrefixExceedance_and_postCrossingBlockPrefixExceedance_eq_mul
        ν length length threshold threshold hthreshold]
      simp [pow_two]
    _ ≤ bound ^ 2 := by
      exact ENNReal.pow_le_pow_left hbound

end ProbabilityTheory.RandomWalk

end
