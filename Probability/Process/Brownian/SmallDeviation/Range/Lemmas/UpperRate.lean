/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Probability.Process.Brownian.SmallDeviation.Corridor.Bounds
import Topology.Order.NNReal.Rational
import Probability.Process.Path.Oscillation.Basic
import Probability.Process.Path.Scaling.UnitInterval
import MeasureTheory.Measure.ContinuousMap.RangeOscillation
import MeasureTheory.MeasurableSpace.ContinuousMap.Oscillation

/-!
# Internal positivity and exponential-limit lemmas for Brownian range rates

These two supporting facts supply positivity of the Brownian range mass and
the exponential decay of the finite-cover corridor term. They support the
finite-cover logarithmic rate in the parent `UpperRate.lean` module.

## Internal proof declarations

- `brownianRangeOscillationMass_ne_zero` obtains positivity from a centered
  closed-corridor lower bound.
- `tendsto_corridorExponential_nhdsGT_zero` composes the inverse-square
  divergence with Mathlib's exponential limit.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology ENNReal

namespace ProbabilityTheory.Process.Brownian.SmallDeviation.Range

open ProbabilityTheory.Process.Path

/-- A Brownian path confined to a centered closed corridor has range
oscillation at most its width. -/
lemma brownianRangeOscillationMass_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} (hwidth : 0 < width) :
    rangeOscillationMass (P := P) hcontinuous width ≠ 0 := by
  let pathLaw := P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
  have hBrownian : IsBrownianReal B P := ⟨hB, ae_of_all P hcontinuous⟩
  let Bpre := hBrownian.toIsPreBrownianReal
  let Bc := Bpre.continuousModification
  have hBccontinuous : ∀ ω, Continuous (Bc · ω) :=
    Bpre.continuous_continuousModification
  have hpathEq : ∀ᵐ ω ∂P, ∀ q : ℚ≥0,
      Bc ((q : ℝ≥0)) ω =
        B ((q : ℝ≥0)) ω := by
    rw [ae_all_iff]
    intro q
    exact Bpre.continuousModification_ae_eq ((q : ℝ≥0))
  have hmapEq :
      (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath Bc hBccontinuous) =ᵐ[P]
      (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath B hcontinuous) := by
    filter_upwards [hpathEq] with ω hω
    have hprocessEq : (fun t : NNReal => Bc t ω) = fun t => B t ω := by
      apply Continuous.ext_on
        NNRat.denseRange_cast_nnreal
        (hBccontinuous ω) (hcontinuous ω)
      rintro _ ⟨q, rfl⟩
      exact hω q
    have hpathEq :
        ProbabilityTheory.continuousunitIntervalPath Bc hBccontinuous ω =
          ProbabilityTheory.continuousunitIntervalPath B hcontinuous ω := by
      ext t
      simp only [ProbabilityTheory.continuousunitIntervalPath_apply]
      exact congrFun hprocessEq (unitInterval.toNNReal t)
    change Skorokhod.ofContinuousMap
        (ProbabilityTheory.continuousunitIntervalPath Bc hBccontinuous ω) =
      Skorokhod.ofContinuousMap
        (ProbabilityTheory.continuousunitIntervalPath B hcontinuous ω)
    rw [hpathEq]
  have hclosed := IsBrownianReal.measure_closedCorridor_lowerBound_of_rho_width
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hwidth hBrownian
  rw [Measure.map_congr hmapEq] at hclosed
  have hsub : (Skorokhod.ofContinuousMap) ⁻¹'
      Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2) ⊆
      ContinuousMap.rangeOscillationSet width := by
    intro path hpath
    change ∀ t, -(width / 2) ≤ Skorokhod.ofContinuousMap path t ∧
      Skorokhod.ofContinuousMap path t ≤ width / 2 at hpath
    simp only [Skorokhod.ofContinuousMap_apply] at hpath
    change path ∈ ContinuousMap.rangeOscillationSet width
    simp only [ContinuousMap.rangeOscillationSet,
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
        rangeOscillationMass (P := P) hcontinuous width := by
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

/-- The corridor eigenvalue exponential tends to zero as its diffusive width
shrinks to zero through positive values. -/
lemma tendsto_corridorExponential_nhdsGT_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun width : ℝ => Real.exp (-(Real.pi ^ 2) /
      (2 * (c * width) ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscaled : Tendsto (fun width : ℝ => c * width)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun width : ℝ => c * width) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with width hwidth
      exact mul_pos hc hwidth
  have hscaledZero : Tendsto (fun width : ℝ => c * width)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hscaled.mono_right nhdsWithin_le_nhds
  have hsquare : Tendsto (fun width : ℝ => (c * width) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using hscaledZero.pow 2, ?_⟩
    filter_upwards [hscaled.eventually self_mem_nhdsWithin] with width hwidth
    exact sq_pos_of_pos hwidth
  have hinv := tendsto_inv_nhdsGT_zero.comp hsquare
  have hcoef : 0 < Real.pi ^ 2 / 2 := by positivity
  have hlarge := hinv.const_mul_atTop hcoef
  have hnegative : Tendsto (fun width : ℝ =>
      -(Real.pi ^ 2 / 2 * ((c * width) ^ 2)⁻¹))
      (𝓝[>] (0 : ℝ)) atBot := by
    exact tendsto_neg_atTop_atBot.comp hlarge
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with width hwidth
  have hne : c * width ≠ 0 := ne_of_gt (mul_pos hc hwidth)
  apply congrArg Real.exp
  field_simp [hne]


end ProbabilityTheory.Process.Brownian.SmallDeviation.Range
