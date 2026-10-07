/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer
import Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw
import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Stable endpoint-rate transfer

This adapter connects the legacy stable endpoint-corridor comparison to the
module-based open-set Portmanteau and discrete return interfaces.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Stable endpoint-constrained escape rates give a sharp exponential lower
bound for the seven open endpoint bands after spatially scaling the limiting
path law. The Ioc source endpoint window is kept strictly inside each Ioo
window used by the open-set Portmanteau transfer. -/
theorem eventually_scaledStableEndpointBandProbability_ge_exp
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {radius epsilon delta : ℝ}
    (hradius : 0 < radius) (hepsilon : 0 < epsilon)
    (hmargin : 4 * epsilon < radius) (hdelta : 0 < delta) :
    ∀ᶠ scale : ℝ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / radius ^ α - delta) * scale ^ α)) <
          (P.map (Skorokhod.scalePath scale))
            (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
  have hbase := HasStableProcessEscapeRate.tendsto_stableRangeLogRate_of_isStableLevyProcess
    hEscape hX
  have hCneg : C < 0 := hEscape.negative
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hCneg (Real.rpow_pos_of_pos hradius α)
  have hmass : ∀ᶠ scale : ℝ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / radius ^ α - delta) * scale ^ α)) <
          shiftedEndpointCorridorProbability Q X 0
            ((((i : ℝ) - 1 / 2) * epsilon) / radius)
            ((((i : ℝ) + 1 / 2) * epsilon) / radius)
            (radius / scale) := by
    apply (Finset.Icc (-3 : ℤ) 3).eventually_all.2
    intro i hi
    have hiabs : |(i : ℝ)| ≤ 3 := by
      rw [abs_le]
      constructor
      · exact_mod_cast (Finset.mem_Icc.mp hi).1
      · exact_mod_cast (Finset.mem_Icc.mp hi).2
    let innerLower : ℝ := ((((i : ℝ) - 1 / 2) * epsilon) / radius)
    let innerUpper : ℝ := ((((i : ℝ) + 1 / 2) * epsilon) / radius)
    have hinnerLower : -1 < innerLower := by
      dsimp [innerLower]
      rw [lt_div_iff₀ hradius]
      nlinarith [abs_le.mp hiabs, hepsilon, hmargin]
    have hinnerUpper : innerUpper < 1 := by
      dsimp [innerUpper]
      rw [div_lt_iff₀ hradius]
      nlinarith [abs_le.mp hiabs, hepsilon, hmargin]
    have hinnerOrder : innerLower < innerUpper := by
      dsimp [innerLower, innerUpper]
      apply div_lt_div_of_pos_right _ hradius
      nlinarith [hepsilon]
    have hrateI := hX.tendsto_inv_rpow_mul_log_shiftedEndpointCorridorProbability
      hcdf hbase (by norm_num : -1 < (0 : ℝ) ∧ (0 : ℝ) < 1)
      hinnerLower hinnerOrder hinnerUpper.le hradius
    filter_upwards [hrateI.eventually
        (Ioi_mem_nhds (by linarith :
          C / radius ^ α - delta < C / radius ^ α)),
      hrateI.eventually (Iio_mem_nhds hrate),
      eventually_gt_atTop (0 : ℝ)] with scale hlogRate hlogUpper hscale
    have hscalePow : 0 < scale ^ α := Real.rpow_pos_of_pos hscale α
    have hinv : scale⁻¹ ^ α = (scale ^ α)⁻¹ := Real.inv_rpow hscale.le α
    have hdiv : C / radius ^ α - delta <
        Real.log ((shiftedEndpointCorridorProbability Q X 0
          innerLower innerUpper (radius / scale)).toReal) / scale ^ α := by
      rw [hinv] at hlogRate
      simpa [div_eq_mul_inv, mul_comm, innerLower, innerUpper] using hlogRate
    have hlog : (C / radius ^ α - delta) * scale ^ α <
        Real.log ((shiftedEndpointCorridorProbability Q X 0
          innerLower innerUpper (radius / scale)).toReal) :=
      (lt_div_iff₀ hscalePow).mp hdiv
    have hlogNeg : scale⁻¹ ^ α *
        Real.log ((shiftedEndpointCorridorProbability Q X 0
          innerLower innerUpper (radius / scale)).toReal) < 0 :=
      hlogUpper
    have hprobPos : 0 <
        (shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
          (radius / scale)).toReal := by
      by_contra hnot
      have hzero :
          (shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
          (radius / scale)).toReal = 0 :=
        le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
      rw [hzero, Real.log_zero, mul_zero] at hlogNeg
      exact (lt_irrefl 0 hlogNeg)
    have hexp' : Real.exp ((C / radius ^ α - delta) * scale ^ α) <
        Real.exp (Real.log
          (shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
            (radius / scale)).toReal) :=
      Real.exp_lt_exp.mpr hlog
    have hexp : Real.exp ((C / radius ^ α - delta) * scale ^ α) <
        (shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
          (radius / scale)).toReal := by
      rwa [Real.exp_log hprobPos] at hexp'
    have hmassFinite :
        shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
          (radius / scale) ≠ ∞ := by
      exact ne_of_lt (measure_lt_top Q _)
    have hmassLower : ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta) * scale ^ α)) <
        shiftedEndpointCorridorProbability Q X 0 innerLower innerUpper
          (radius / scale) := by
      apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hmassFinite).mp
      simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hexp
    exact hmassLower
  filter_upwards [hmass, eventually_gt_atTop (0 : ℝ)] with scale hmassScale hscale
  intro i hi
  let lowerOuter : ℝ := (((i : ℝ) - 1) * epsilon) / scale
  let upperOuter : ℝ := (((i : ℝ) + 1) * epsilon) / scale
  let lowerInner : ℝ := (((i : ℝ) - 1 / 2) * epsilon) / scale
  let upperInner : ℝ := (((i : ℝ) + 1 / 2) * epsilon) / scale
  have hmapSet : (Skorokhod.scalePath scale) ⁻¹'
      Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
        (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon) =
      Skorokhod.rangeInOpenIntervalEndsIn
        (-radius / scale) (radius / scale) lowerOuter upperOuter := by
    ext path
    exact Skorokhod.mem_rangeInOpenIntervalEndsIn_scalePath_iff hscale path
  have hmapProbability :
      (P.map (Skorokhod.scalePath scale))
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) =
        P (Skorokhod.rangeInOpenIntervalEndsIn
        (-radius / scale) (radius / scale) lowerOuter upperOuter) := by
    have hmeas : Measurable (Skorokhod.scalePath scale) :=
      (Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)).measurable
    rw [Measure.map_apply hmeas
      (Skorokhod.measurableSet_rangeInOpenIntervalEndsIn
        (-radius) radius (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)),
      hmapSet]
  have hprocessLaw := hEscape.isStableClockProcessLaw.measure_corridorReturnEvent_eq
    hX (-radius / scale) (radius / scale) lowerOuter upperOuter
  have hIocSubset :
      fullSegmentCorridorIocReturnEvent X 0 1 (-radius / scale) (radius / scale)
        lowerInner upperInner ⊆
      fullSegmentCorridorReturnEvent X 0 1 (-radius / scale) (radius / scale)
        lowerOuter upperOuter := by
    change segmentCorridorEndpointEvent X 0 1 (-radius / scale) (radius / scale)
        (Set.Ioc lowerInner upperInner) ⊆
      segmentCorridorEndpointEvent X 0 1 (-radius / scale) (radius / scale)
        (Set.Ioo lowerOuter upperOuter)
    apply segmentCorridorEndpointEvent_mono X 0 1 le_rfl le_rfl
    intro x hx
    simp only [Set.mem_Ioc, Set.mem_Ioo] at hx ⊢
    constructor
    · have hlow : lowerOuter < lowerInner := by
        dsimp [lowerOuter, lowerInner]
        apply div_lt_div_of_pos_right _ hscale
        nlinarith [hepsilon]
      exact lt_trans hlow hx.1
    · have hupp : upperInner < upperOuter := by
        dsimp [upperInner, upperOuter]
        apply div_lt_div_of_pos_right _ hscale
        nlinarith [hepsilon]
      exact lt_of_le_of_lt hx.2 hupp
  have hIocEq :
      shiftedEndpointCorridorProbability Q X 0
          ((((i : ℝ) - 1 / 2) * epsilon) / radius)
          ((((i : ℝ) + 1 / 2) * epsilon) / radius) (radius / scale) =
        Q (fullSegmentCorridorIocReturnEvent X 0 1 (-radius / scale)
          (radius / scale) lowerInner upperInner) := by
    simp [shiftedEndpointCorridorProbability, lowerInner, upperInner,
      fullSegmentCorridorIocReturnEvent, segmentCorridorEndpointEvent]
    congr 1
    field_simp [hscale.ne', hradius.ne']
  calc
    ENNReal.ofReal (Real.exp ((C / radius ^ α - delta) * scale ^ α)) <
        shiftedEndpointCorridorProbability Q X 0
          ((((i : ℝ) - 1 / 2) * epsilon) / radius)
          ((((i : ℝ) + 1 / 2) * epsilon) / radius) (radius / scale) :=
      hmassScale i hi
    _ = Q (fullSegmentCorridorIocReturnEvent X 0 1 (-radius / scale)
        (radius / scale) lowerInner upperInner) := hIocEq
    _ ≤ Q (fullSegmentCorridorReturnEvent X 0 1 (-radius / scale)
        (radius / scale) lowerOuter upperOuter) := measure_mono hIocSubset
    _ = P (Skorokhod.rangeInOpenIntervalEndsIn
        (-radius / scale) (radius / scale) lowerOuter upperOuter) := hprocessLaw.symm
    _ = (P.map (Skorokhod.scalePath scale))
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := hmapProbability.symm


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
