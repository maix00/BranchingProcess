/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.HittingTime.Declarations
public import Probability.Process.RandomWalk.Path.Block.Law.StoppingTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# First crossings and a following IID excursion

The first partial sum to cross a fixed threshold is a stopping time for the
increment filtration. At that time, a finite excursion of fresh increments
factors from the event that the crossing occurred in a prescribed initial
window. This is an exact event-level factorization; it does not identify the
resulting event with a general two-sided path-modulus event.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The first number of increments at which the partial sum from the origin
reaches `threshold`, or `⊤` if it never does. -/
noncomputable def firstPrefixExceedanceTime (threshold : ℝ) :
    (ℕ → ℝ) → WithTop ℕ :=
  ProbabilityTheory.firstDeclaredSuccess
    (fun n => {path | threshold ≤ |AdditivePath.displacement n path|})

/-- The first prefix-exceedance time is a stopping time for the filtration
which reveals exactly the increments already used by each partial sum. -/
theorem firstPrefixExceedanceTime_isStoppingTime (threshold : ℝ) :
    IsStoppingTime (sequencePrefixFiltration (E := ℝ))
      (firstPrefixExceedanceTime threshold) := by
  apply ProbabilityTheory.firstDeclaredSuccess_isStoppingTime
  intro n
  have hdisplacement :
      Measurable[sequencePrefixFiltration (E := ℝ) n]
        (AdditivePath.displacement n) := by
    unfold AdditivePath.displacement
    exact Finset.measurable_sum (Finset.range n) fun k hk =>
      sequenceCoordinate_measurable n ⟨k, Finset.mem_range.mp hk⟩
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp hdisplacement)

/-- A first prefix crossing occurs by time `length` exactly when the
corresponding finite-prefix excursion occurs. Positivity excludes a crossing
at time zero. -/
theorem firstPrefixExceedanceTime_le_iff_blockPrefixExceedance
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (length : ℕ) (path : ℕ → ℝ) :
    firstPrefixExceedanceTime threshold path ≤ length ↔
      path ∈ blockPrefixExceedance 0 length threshold := by
  change ProbabilityTheory.firstDeclaredSuccess
    (fun n => {path | threshold ≤ |AdditivePath.displacement n path|}) path ≤ length ↔ _
  rw [ProbabilityTheory.firstDeclaredSuccess_le_iff]
  constructor
  · rintro ⟨n, hnle, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := by omega
      subst n
      have hleZero : threshold ≤ 0 := by
        simpa [AdditivePath.displacement] using hn
      linarith
    refine ⟨⟨n - 1, by omega⟩, ?_⟩
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    simp only [Nat.zero_add]
    rw [show n - 1 + 1 = n by omega]
    exact hn
  · rintro ⟨k, hk⟩
    refine ⟨k.val + 1, by omega, ?_⟩
    have hsum : AdditivePath.blockSum 0 (k.val + 1) path =
        AdditivePath.displacement (k.val + 1) path := by
      rw [AdditivePath.blockSum_eq_displacement_natAdd]
      simp only [Nat.zero_add]
    rw [hsum] at hk
    exact hk

/-- On a finite first-crossing cell, an excursion of the next block has the
same probability as an excursion in a deterministic initial block. -/
theorem measure_inter_boundedStoppingTime_blockPrefixExceedanceAfter_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := ℝ)) τ)
    (timeBound futureLength : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν)
        ({path | τ path ≤ timeBound} ∩
          blockPrefixExceedanceAfter τ futureLength threshold) =
      (iidSequenceLaw ν) {path | τ path ≤ timeBound} *
        (iidSequenceLaw ν) (blockPrefixExceedance 0 futureLength threshold) := by
  rw [blockPrefixExceedanceAfter_eq_iidBlockEventAfter,
    ← blockPrefixExceedance_eq_preimage_blockCoordinates 0 futureLength threshold]
  exact iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul
    ν τ hτ timeBound futureLength
    (blockPrefixExceedanceOnCoordinates futureLength threshold)
    (measurableSet_blockPrefixExceedanceOnCoordinates futureLength threshold)

/-- The event that a first prefix excursion occurs by `firstLength`, followed
by an excursion of fresh increments after its first crossing, factors exactly
into the two one-block probabilities. -/
theorem measure_firstPrefixExceedance_and_postCrossingBlockPrefixExceedance_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (firstLength futureLength : ℕ) (firstThreshold futureThreshold : ℝ)
    (hfirstThreshold : 0 < firstThreshold) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance 0 firstLength firstThreshold ∩
          blockPrefixExceedanceAfter (firstPrefixExceedanceTime firstThreshold)
            futureLength futureThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance 0 firstLength firstThreshold) *
        (iidSequenceLaw ν) (blockPrefixExceedance 0 futureLength futureThreshold) := by
  have hfirstEvent : blockPrefixExceedance 0 firstLength firstThreshold =
      {path | firstPrefixExceedanceTime firstThreshold path ≤ firstLength} := by
    ext path
    exact (firstPrefixExceedanceTime_le_iff_blockPrefixExceedance
      firstThreshold hfirstThreshold firstLength path).symm
  rw [hfirstEvent]
  exact measure_inter_boundedStoppingTime_blockPrefixExceedanceAfter_eq_mul
    ν (firstPrefixExceedanceTime firstThreshold)
    (firstPrefixExceedanceTime_isStoppingTime firstThreshold)
    firstLength futureLength futureThreshold

/-! ## Two ordered excursions in a finite window

The event below is a discrete modulus event: two increments of the partial
sum path, in time order and within one finite window, both exceed a fixed
size. A first-crossing argument reduces it to a crossing followed by a fresh
excursion. This is the probabilistic core of the usual iid J1 tightness
estimate and does not depend on a stable-domain assumption.
-/

/-- Two ordered oscillations of the partial-sum path, with both endpoint
pairs contained in the first `length` increments. -/
def twoOrderedPrefixExcursions (length : ℕ) (threshold : ℝ) : Set (ℕ → ℝ) :=
  {path | ∃ i j k l : ℕ,
    i ≤ j ∧ j ≤ k ∧ k ≤ l ∧ l ≤ length ∧
      threshold ≤ |AdditivePath.displacement j path -
        AdditivePath.displacement i path| ∧
      threshold ≤ |AdditivePath.displacement l path -
        AdditivePath.displacement k path|}

private theorem abs_sub_le_sum_abs (x y : ℝ) :
    |x - y| ≤ |x| + |y| := by
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [le_abs_self x, neg_le_abs x,
    le_abs_self y, neg_le_abs y]

private theorem split_abs_sub_le {threshold x y : ℝ}
    (hlarge : 2 * threshold ≤ |x - y|) :
    threshold ≤ |x| ∨ threshold ≤ |y| := by
  by_contra h
  push Not at h
  have htriangle := abs_sub_le_sum_abs x y
  linarith

theorem blockPrefixExceedance_of_displacementDifference
    (path : ℕ → ℝ) {start finish length : ℕ} {threshold : ℝ}
    (hpositive : 0 < threshold) (hstart : start ≤ finish)
    (hlength : finish - start ≤ length)
    (hlarge : threshold ≤ |AdditivePath.displacement finish path -
      AdditivePath.displacement start path|) :
    path ∈ blockPrefixExceedance start length threshold := by
  have hne : start < finish := by
    by_contra h
    have heq : finish = start := by omega
    subst finish
    simp at hlarge
    linarith
  let k : Fin length := ⟨finish - start - 1, by omega⟩
  refine ⟨k, ?_⟩
  rw [show k.val + 1 = finish - start by dsimp [k]; omega,
    AdditivePath.blockSum_eq_displacement_natAdd]
  have hsplit := AdditivePath.displacement_add start (finish - start) path
  have hfinish : start + (finish - start) = finish := by omega
  rw [hfinish] at hsplit
  have hdiff : AdditivePath.displacement finish path -
      AdditivePath.displacement start path =
        AdditivePath.displacement (finish - start)
          (fun m => path (start + m)) := by
    rw [hsplit]
    ring
  rw [← hdiff]
  exact hlarge

private theorem twoOrderedPrefixExcursions_subset_firstCrossing
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
