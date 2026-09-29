module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Diffusive.Brownian
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Range.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Small-width logarithmic bound for Brownian range events

The corrected fixed finite corridor cover gives the Brownian range event a
finite sum of full-spectrum corridor bounds.  This file extracts its
small-width exponential rate without introducing a minimum over the
approximating lattice walk.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

noncomputable def brownianRangeOscillationMass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ}
    (hcontinuous : ∀ ω, Continuous (B · ω)) (width : ℝ) : ENNReal :=
  P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
    (ProbabilityTheory.Process.Path.rangeOscillationSet width)

/-- At a fixed finite-cover count, the Brownian range event is bounded by the
complete-spectrum geometric correction for corridors of width
`width * (1 + 3 / count)`. -/
theorem brownianRangeOscillationMass_le_fixedSpectralSum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    brownianRangeOscillationMass (P := P) hcontinuous width ≤
      ∑ _j : Fin count, ENNReal.ofReal (4 *
        (Real.exp (-(Real.pi ^ 2) /
            (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) /
            (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2))))) := by
  have h := brownianRangeOscillation_le_fixedSpectralCover
    hB hcontinuous hmeasurable hwidth hcount
  have hcorridor : width + 3 * (width / (count : ℝ)) =
      (1 + 3 / (count : ℝ)) * width := by
    field_simp
  rw [brownianRangeOscillationMass]
  simpa only [hcorridor] using h

/-- Once the fixed corridor eigenvalue is below `1/2`, the full-spectrum
geometric correction is at most twice its leading exponential.  The finite
cover contributes only its fixed cardinality. -/
theorem brownianRangeOscillationMass_le_smallWidthExponential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count)
    (hsmall : Real.exp (-(Real.pi ^ 2) /
      (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)) < 1 / 2) :
    brownianRangeOscillationMass (P := P) hcontinuous width ≤
      ENNReal.ofReal ((count : ℝ) * (8 * Real.exp (-(Real.pi ^ 2) /
        (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)))) := by
  let r : ℝ := Real.exp (-(Real.pi ^ 2) /
    (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2))
  have hrpos : 0 < r := by positivity
  have hden : 0 < 1 - r := by linarith [hsmall]
  have hratio : 4 * (r / (1 - r)) ≤ 8 * r := by
    rw [div_le_iff₀ hden]
    dsimp [r] at *
    nlinarith
  have hcover := brownianRangeOscillationMass_le_fixedSpectralSum
    hB hcontinuous hmeasurable hwidth hcount
  calc
    brownianRangeOscillationMass (P := P) hcontinuous width ≤
        ∑ _j : Fin count, ENNReal.ofReal (4 * (r / (1 - r))) := by
      simpa [r] using hcover
    _ ≤ ∑ _j : Fin count, ENNReal.ofReal (8 * r) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal hratio
    _ = ENNReal.ofReal ((count : ℝ) * (8 * r)) := by
      rw [Finset.sum_const_zero]
      rw [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity)]
      simp [r]

/-- A Brownian path confined to a centered closed corridor has range
oscillation at most its width.  This transfers the existing positive
Brownian corridor lower bound to strict positivity of the range event. -/
theorem brownianRangeOscillationMass_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} (hwidth : 0 < width) :
    brownianRangeOscillationMass (P := P) hcontinuous width ≠ 0 := by
  let pathLaw := P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
  have hclosed := ofReal_exp_neg_pi_sq_div_two_rho_sq_width_sq_le_brownian_closedCorridor
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hwidth hB hcontinuous hmeasurable
  have hsub : (Skorokhod.ofContinuousMap) ⁻¹'
      Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2) ⊆
      ProbabilityTheory.Process.Path.rangeOscillationSet width := by
    intro path hpath
    change ∀ t, -(width / 2) ≤ Skorokhod.ofContinuousMap path t ∧
      Skorokhod.ofContinuousMap path t ≤ width / 2 at hpath
    simp only [Skorokhod.ofContinuousMap_apply] at hpath
    change path ∈ ProbabilityTheory.Process.Path.rangeOscillationSet width
    simp only [ProbabilityTheory.Process.Path.rangeOscillationSet,
      Set.mem_iInter, Set.mem_ofPred_eq]
    intro s t
    apply abs_sub_le_iff.mpr
    constructor
    · have hs := (hpath s).2
      have ht := (hpath t).1
      nlinarith
    · have hs := (hpath s).1
      have ht := (hpath t).2
      nlinarith
  have hmap : pathLaw.map Skorokhod.ofContinuousMap =
      P.map (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath B hcontinuous) := by
    dsimp [pathLaw]
    rw [Measure.map_map]
    · exact Skorokhod.measurable_ofContinuousMap
    · exact ProbabilityTheory.measurable_continuousunitIntervalPath
        B hcontinuous hmeasurable
  have hle :
      P.map (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) ≤
        brownianRangeOscillationMass (P := P) hcontinuous width := by
    rw [← hmap, Measure.map_apply Skorokhod.measurable_ofContinuousMap
      (Skorokhod.isClosed_rangeInClosedInterval _ _).measurableSet]
    exact measure_mono hsub
  intro hz
  have hpos : 0 < ENNReal.ofReal
      (Real.exp (-(Real.pi ^ 2) /
        (2 * (1 / 2 : ℝ) ^ 2 * width ^ 2))) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hlower := hclosed.trans hle
  rw [hz] at hlower
  exact (not_le_of_gt hpos) hlower

end ProbabilityTheory.RandomWalk.Mogulskii

end
