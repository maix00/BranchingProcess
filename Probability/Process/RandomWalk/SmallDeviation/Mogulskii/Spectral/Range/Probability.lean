/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds

/-!
# Rademacher range probabilities from interval survival

A finite-time path whose oscillation is at most an integer width fits in one
of finitely many translates of an interval.  The killed-kernel estimate then
turns that cover into an explicit finite-time upper bound.  At diffusive
width the resulting prefactor grows with the approximation length, so this
estimate alone does not transfer a sharp upper bound through Donsker's
theorem; the sharp route uses a fixed finite cover of Brownian corridor
locations and the full-spectrum geometric estimate instead.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The event that the Rademacher path, after translation to an interior
lattice site, stays in a finite interval. -/
def shiftedRademacherIntervalEvent (width n : ℕ)
    (shift : Fin (width + 1)) : Set (ℕ → Bool) :=
  {branch | rademacherStaysInInterval (width + 1) n (intervalSite shift) branch}

/-- Every path with oscillation at most `width` belongs to one of the
translated killed-interval survival events. -/
theorem rademacherOscillation_subset_intervalCover
    (n width : ℕ) :
    {branch | RademacherOscillationBounded n width branch} ⊆
      ⋃ shift ∈ Finset.univ, shiftedRademacherIntervalEvent width n shift := by
  intro branch hosc
  obtain ⟨shift, hshift⟩ :=
    exists_shift_of_rademacherOscillation n width branch hosc
  have hclosed : InClosedInterval (1 : ℝ) ((width + 1 : ℕ) : ℝ) n
      (intervalSite shift)
      (rademacherIncrementPath branch) := by
    change ∀ k : Fin (n + 1),
      intervalSite shift +
          AdditivePath.displacement (k : ℕ) (rademacherIncrementPath branch) ∈
        Set.Icc (1 : ℝ) ((width + 1 : ℕ) : ℝ)
    intro k
    have hk := hshift k
    change (shift.val : ℝ) +
        AdditivePath.displacement (k : ℕ) (rademacherIncrementPath branch) ∈
      Set.Icc 0 (width : ℝ) at hk
    have hsite : intervalSite shift = (shift.val : ℝ) + 1 := by
      simp [intervalSite]
    rw [hsite]
    have hupper : ((width + 1 : ℕ) : ℝ) = (width : ℝ) + 1 := by
      norm_cast
    rw [hupper]
    simp only [Set.mem_Icc] at hk ⊢
    constructor <;> linarith
  have hstay :=
    (rademacherStaysInInterval_iff_inClosedInterval n shift branch).mpr hclosed
  simp only [Set.mem_iUnion, Finset.mem_univ]
  exact ⟨shift, trivial, hstay⟩

/-- The oscillation probability is bounded by the sum of the killed-interval
survival probabilities over all possible integer minima. -/
theorem iidRademacher_oscillation_le_intervalSurvival_sum
    (n width : ℕ) :
    iidSequenceLaw fairBoolMeasure
        {branch | RademacherOscillationBounded n width branch} ≤
      ∑ shift ∈ Finset.univ,
        Kernel.remainingMass (intervalRademacherKernel (width + 1)) n shift := by
  calc
    iidSequenceLaw fairBoolMeasure
        {branch | RademacherOscillationBounded n width branch} ≤
      iidSequenceLaw fairBoolMeasure
        (⋃ shift ∈ Finset.univ,
          shiftedRademacherIntervalEvent width n shift) :=
      measure_mono (rademacherOscillation_subset_intervalCover n width)
    _ ≤ ∑ shift ∈ Finset.univ,
          iidSequenceLaw fairBoolMeasure
            (shiftedRademacherIntervalEvent width n shift) :=
      measure_biUnion_finset_le _ _
    _ = ∑ shift ∈ Finset.univ,
          Kernel.remainingMass (intervalRademacherKernel (width + 1)) n shift := by
      apply Finset.sum_congr rfl
      intro shift _hshift
      rw [show shiftedRademacherIntervalEvent width n shift =
          {branch | rademacherStaysInInterval (width + 1) n
            (intervalSite shift) branch} by rfl,
        ← intervalRademacherKernel_pow_apply_univ_eq_pathSurvival]
      rfl

/-- Uniform finite-time spectral form of the lattice-minimum cover.  This is a
valid discrete inequality, but its width-dependent prefactor is too large to
yield the sharp Brownian range estimate at diffusive width. -/
theorem iidRademacher_oscillation_le_uniform_spectral_bound
    (n width : ℕ) (hwidth : 0 < width) :
    iidSequenceLaw fairBoolMeasure
        {branch | RademacherOscillationBounded n width branch} ≤
      (↑(width + 1) : ENNReal) * ENNReal.ofReal
        (Real.cos (Real.pi / (width + 2 : ℕ)) ^ n /
          Real.sin (Real.pi / (width + 2 : ℕ))) := by
  calc
    iidSequenceLaw fairBoolMeasure
        {branch | RademacherOscillationBounded n width branch} ≤
      ∑ shift ∈ Finset.univ,
        Kernel.remainingMass (intervalRademacherKernel (width + 1)) n shift :=
      iidRademacher_oscillation_le_intervalSurvival_sum n width
    _ ≤ ∑ shift ∈ Finset.univ,
        ENNReal.ofReal
          (Real.cos (Real.pi / (width + 2 : ℕ)) ^ n /
            Real.sin (Real.pi / (width + 2 : ℕ))) := by
      apply Finset.sum_le_sum
      intro shift _hshift
      have hcount : 1 < width + 1 := by omega
      exact (intervalRademacherKernel_remainingMass_uniform_bounds
        hcount n shift).2
    _ = (↑(width + 1) : ENNReal) * ENNReal.ofReal
        (Real.cos (Real.pi / (width + 2 : ℕ)) ^ n /
          Real.sin (Real.pi / (width + 2 : ℕ))) := by
      simp

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
