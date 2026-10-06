/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.HittingTime.Declarations
public import Probability.Process.RandomWalk.Path.Block.Law.StoppingTime

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

end ProbabilityTheory.RandomWalk

end
