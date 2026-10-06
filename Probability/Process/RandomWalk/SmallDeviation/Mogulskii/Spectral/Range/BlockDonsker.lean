/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Continuous
public import Probability.Process.RandomWalk.Path.Corridor.Interpolation
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal
public import Probability.Process.Path.Oscillation

/-!
# Donsker upper bound for a single oscillation block

This is the corrected route from the discrete block comparison to Brownian
spectral decay. A finite increment block is first identified with the grid
vertices of its polygonal interpolation. The closed range-oscillation event
then transfers through Donsker without taking a union over individual times.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.Process.Path

/-- If all grid vertices of a polygonal path have range diameter at most
`width`, then the entire interpolation has the same range bound. -/
theorem normalizedLinearContinuousPathIcc_mem_rangeOscillationSet_of_grid
    {length : ℕ} (hlength : 0 < length) {scale width : ℝ}
    (increment : ℕ → ℝ)
    (hvertices : ∀ i j : Fin (length + 1),
      |(scale⁻¹ * AdditivePath.displacement i increment) -
        (scale⁻¹ * AdditivePath.displacement j increment)| ≤ width) :
    normalizedLinearContinuousPathIcc (fun _ => scale) length increment ∈
      ProbabilityTheory.Process.Path.rangeOscillationSet width := by
  classical
  let value : Fin (length + 1) → ℝ := fun i => scale⁻¹ * AdditivePath.displacement i increment
  obtain ⟨imin, hmin⟩ := Finite.exists_min value
  obtain ⟨imax, hmax⟩ := Finite.exists_max value
  let lower := value imin
  let upper := value imax
  have hzero : value (0 : Fin (length + 1)) = 0 := by
    simp [value]
  have hlower : lower ≤ 0 := by
    rw [← hzero]
    exact hmin 0
  have hupper : 0 ≤ upper := by
    rw [← hzero]
    exact hmax 0
  have hspan : upper - lower ≤ width := by
    have h := hvertices imax imin
    dsimp [value, upper, lower] at h ⊢
    exact (abs_le.mp h).2
  have hpathRange :
      Set.range (normalizedLinearContinuousPathIcc
          (fun _ => scale) length increment) ⊆ Set.Icc lower upper := by
    apply (normalizedLinearContinuousPathIcc_range_subset_iff
      (fun _ => scale) hlength (convex_Icc lower upper)
      ⟨hlower, hupper⟩ increment).2
    intro k
    have hkmin := hmin ⟨k.val + 1, by omega⟩
    have hkmax := hmax ⟨k.val + 1, by omega⟩
    constructor
    · simpa [value, lower] using hkmin
    · simpa [value, upper] using hkmax
  simp only [ProbabilityTheory.Process.Path.rangeOscillationSet,
    Set.mem_iInter, Set.mem_ofPred_eq]
  intro s t
  have hs := hpathRange ⟨s, rfl⟩
  have ht := hpathRange ⟨t, rfl⟩
  have hst : normalizedLinearContinuousPathIcc
      (fun _ => scale) length increment s -
      normalizedLinearContinuousPathIcc (fun _ => scale) length increment t ≤
        width := by
    calc
      _ ≤ upper - lower := sub_le_sub hs.2 ht.1
      _ ≤ width := hspan
  have hts : -(width) ≤ normalizedLinearContinuousPathIcc
      (fun _ => scale) length increment s -
      normalizedLinearContinuousPathIcc (fun _ => scale) length increment t := by
    have h := sub_le_sub ht.2 hs.1
    linarith
  exact abs_le.mpr ⟨hts, hst⟩

/-- A finite block oscillation event is contained in the corresponding
closed range-oscillation event for its normalized polygonal path. -/
theorem blockOscillationEvent_subset_normalizedPath_rangeOscillation
    {length : ℕ} (hlength : 0 < length) {width scale : ℝ}
    (hscale : 0 < scale) :
    {increment : ℕ → ℝ |
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)} ⊆
      (normalizedLinearContinuousPathIcc (fun _ => scale) length) ⁻¹'
        ProbabilityTheory.Process.Path.rangeOscillationSet (width / scale) := by
  intro increment hosc
  apply normalizedLinearContinuousPathIcc_mem_rangeOscillationSet_of_grid
    hlength increment
  intro i j
  have h := hosc i j
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates 0 length increment) i -
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment) j| ≤ width at h
  rw [partialSum_blockCoordinates (start := 0) (increment := increment) i,
    partialSum_blockCoordinates (start := 0) (increment := increment) j] at h
  have hpartial : |AdditivePath.displacement i increment - AdditivePath.displacement j increment| ≤ width := by
    simpa only [AdditivePath.blockSum_zero_start] using h
  have hvalue :
      (scale⁻¹ * AdditivePath.displacement i increment) -
          (scale⁻¹ * AdditivePath.displacement j increment) =
        (AdditivePath.displacement i increment - AdditivePath.displacement j increment) / scale := by
    rw [div_eq_mul_inv]
    ring
  rw [hvalue, abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hpartial (le_of_lt hscale)

/-- The one-block oscillation probability is bounded by the polygonal path
law of its closed range-oscillation event. -/
theorem iidSequenceLaw_blockOscillation_le_normalizedPathLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {length : ℕ} (hlength : 0 < length) {width scale : ℝ}
    (hscale : 0 < scale) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)} ≤
      ProbabilityTheory.RandomWalk.normalizedLinearPathLaw ν
        (fun _ => scale) length
        (ProbabilityTheory.Process.Path.rangeOscillationSet (width / scale)) := by
  rw [ProbabilityTheory.RandomWalk.normalizedLinearPathLaw,
    Measure.map_apply
      (ProbabilityTheory.RandomWalk.measurable_normalizedLinearContinuousPathIcc
        (fun _ => scale) length)
      (ProbabilityTheory.Process.Path.measurableSet_rangeOscillationSet _)]
  exact measure_mono
    (blockOscillationEvent_subset_normalizedPath_rangeOscillation
      hlength hscale)

/-- Donsker's closed-set bound for a finite oscillation block whose
normalized widths are eventually bounded by a fixed width. -/
theorem limsup_iidSequenceLaw_blockOscillation_le_brownianRangeOscillationMass
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {length : ℕ → ℕ} (hlength : Tendsto length atTop atTop)
    {blockWidth : ℕ → ℝ} {width : ℝ}
    (hwidth : ∀ᶠ n : ℕ in atTop,
      blockWidth n / Real.sqrt (length n) ≤ width) :
    atTop.limsup (fun n => iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationEvent (blockWidth n) (length n)
        (Combinatorics.Sequence.blockCoordinates 0 (length n) increment)}) ≤
      rangeOscillationMass (P := P) hcontinuous width := by
  let hDonsker := RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_brownian
    ν hcentered hsecondMoment hB hcontinuous hmeasurable
  have hsubsequence := hDonsker.comp_tendsto hlength
  let event : Set C(unitInterval, ℝ) :=
    ProbabilityTheory.Process.Path.rangeOscillationSet width
  have hclosed : IsClosed event :=
    ProbabilityTheory.Process.Path.isClosed_rangeOscillationSet width
  have hport : atTop.limsup (fun n =>
      ProbabilityTheory.RandomWalk.normalizedLinearPathLaw ν
        (fun _ => Real.sqrt (length n)) (length n) event) ≤
      rangeOscillationMass (P := P) hcontinuous width := by
    have hportRaw := hsubsequence.limsup_measure_map_le_of_isClosed hclosed
    convert hportRaw using 1
    · apply limsup_congr
      filter_upwards with n
      rw [ProbabilityTheory.RandomWalk.normalizedLinearPathLaw]
      congr 1
    · rfl
  have hblock : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (blockWidth n) (length n)
          (Combinatorics.Sequence.blockCoordinates 0 (length n) increment)} ≤
      ProbabilityTheory.RandomWalk.normalizedLinearPathLaw ν
        (fun _ => Real.sqrt (length n)) (length n) event := by
    filter_upwards [hwidth, hlength.eventually_gt_atTop 0] with n hnwidth hnlength
    have hsqrt : 0 < Real.sqrt (length n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hnlength)
    have hcmp := iidSequenceLaw_blockOscillation_le_normalizedPathLaw
      ν hnlength (width := blockWidth n) (scale := Real.sqrt (length n)) hsqrt
    have hwidth' : blockWidth n / Real.sqrt (length n : ℝ) ≤ width := hnwidth
    have hmonoevent :
        ProbabilityTheory.Process.Path.rangeOscillationSet
            (blockWidth n / Real.sqrt (length n : ℝ)) ⊆ event := by
      intro path hpath
      change path ∈ ProbabilityTheory.Process.Path.rangeOscillationSet
        (blockWidth n / Real.sqrt (length n : ℝ)) at hpath
      change path ∈ ProbabilityTheory.Process.Path.rangeOscillationSet width
      simp only [ProbabilityTheory.Process.Path.rangeOscillationSet,
        Set.mem_iInter, Set.mem_ofPred_eq] at hpath ⊢
      intro s t
      exact (hpath s t).trans hwidth'
    have hmonomeasure :
        ProbabilityTheory.RandomWalk.normalizedLinearPathLaw ν
          (fun _ => Real.sqrt (length n)) (length n)
          (ProbabilityTheory.Process.Path.rangeOscillationSet
            (blockWidth n / Real.sqrt (length n : ℝ))) ≤
        ProbabilityTheory.RandomWalk.normalizedLinearPathLaw ν
          (fun _ => Real.sqrt (length n)) (length n) event := by
      unfold ProbabilityTheory.RandomWalk.normalizedLinearPathLaw
      exact measure_mono hmonoevent
    have hcmp' := hcmp.trans hmonomeasure
    simpa [event] using hcmp'
  exact (Filter.limsup_le_limsup hblock
    (Filter.isCoboundedUnder_le_of_le atTop fun _ => bot_le)
    (Filter.isBoundedUnder_of_eventually_le
      (a := 1) (Eventually.of_forall fun n => by
        dsimp [ProbabilityTheory.RandomWalk.normalizedLinearPathLaw]
        calc
          (iidSequenceLaw ν).map
              (normalizedLinearContinuousPathIcc
                (fun _ => Real.sqrt (length n)) (length n)) event ≤
              (iidSequenceLaw ν).map
                (normalizedLinearContinuousPathIcc
                  (fun _ => Real.sqrt (length n)) (length n)) Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := by rw [Measure.map_apply
            (measurable_normalizedLinearContinuousPathIcc _ _)
            MeasurableSet.univ]; simp))) |>.trans hport

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
