/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer
public import Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Stable endpoint-rate transfer

This adapter connects the legacy stable endpoint-corridor comparison to the
module-based open-set Portmanteau and discrete return interfaces.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

@[expose] public section

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

/-- Stable endpoint escape rates give a sharp exponential lower bound for an
open endpoint corridor in an arbitrary shifted interval. The interval may be
asymmetric about the origin; its half-width alone determines the rate. The
smaller `Ioc` endpoint window used by the stable process is strictly contained
in the open endpoint interval used by Portmanteau. -/
theorem eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {radius delta d c b : ℝ}
    (hradius : 0 < radius) (hdelta : 0 < delta)
    (hd : -1 < d ∧ d < 1)
    (hc : -1 < c) (hcb : c < b) (hb : b < 1) :
    ∀ᶠ scale : ℝ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / radius ^ α - delta) * scale ^ α)) <
        (P.map (Skorokhod.scalePath scale))
          (Skorokhod.rangeInOpenIntervalEndsIn
            (radius * (d - 1)) (radius * (d + 1))
            (radius * (d + c)) (radius * (d + b))) := by
  have hbase := HasStableProcessEscapeRate.tendsto_stableRangeLogRate_of_isStableLevyProcess
    hEscape hX
  have hCneg : C < 0 := hEscape.negative
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hCneg (Real.rpow_pos_of_pos hradius α)
  let margin : ℝ := (b - c) / 4
  let innerLower : ℝ := c + margin
  let innerUpper : ℝ := b - margin
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  have hinnerLower : c < innerLower := by dsimp [innerLower]; linarith
  have hinnerUpper : innerUpper < b := by dsimp [innerUpper]; linarith
  have hinnerLower_gt : -1 < innerLower := lt_trans hc hinnerLower
  have hinnerUpper_lt : innerUpper < 1 := lt_trans hinnerUpper hb
  have hinnerOrder : innerLower < innerUpper := by
    dsimp [innerLower, innerUpper, margin]
    linarith
  have hmass : ∀ᶠ scale : ℝ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / radius ^ α - delta) * scale ^ α)) <
        shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale) := by
    have hrateI := hX.tendsto_inv_rpow_mul_log_shiftedEndpointCorridorProbability
      hcdf hbase hd hinnerLower_gt hinnerOrder hinnerUpper_lt.le hradius
    filter_upwards [hrateI.eventually
        (Ioi_mem_nhds (by linarith : C / radius ^ α - delta < C / radius ^ α)),
      hrateI.eventually (Iio_mem_nhds hrate), eventually_gt_atTop (0 : ℝ)]
      with scale hlogRate hlogUpper hscale
    have hscalePow : 0 < scale ^ α := Real.rpow_pos_of_pos hscale α
    have hinv : scale⁻¹ ^ α = (scale ^ α)⁻¹ := Real.inv_rpow hscale.le α
    have hdiv : C / radius ^ α - delta <
        Real.log ((shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale)).toReal) / scale ^ α := by
      rw [hinv] at hlogRate
      simpa [div_eq_mul_inv, mul_comm] using hlogRate
    have hlog : (C / radius ^ α - delta) * scale ^ α <
        Real.log ((shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale)).toReal) :=
      (lt_div_iff₀ hscalePow).mp hdiv
    have hlogNeg : scale⁻¹ ^ α *
        Real.log ((shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale)).toReal) < 0 := hlogUpper
    have hprobPos : 0 <
        (shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale)).toReal := by
      by_contra hnot
      have hzero :
          (shiftedEndpointCorridorProbability Q X d innerLower innerUpper
            (radius / scale)).toReal = 0 :=
        le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
      rw [hzero, Real.log_zero, mul_zero] at hlogNeg
      exact (lt_irrefl 0 hlogNeg)
    have hexp' : Real.exp ((C / radius ^ α - delta) * scale ^ α) <
        Real.exp (Real.log
          (shiftedEndpointCorridorProbability Q X d innerLower innerUpper
            (radius / scale)).toReal) := Real.exp_lt_exp.mpr hlog
    have hexp : Real.exp ((C / radius ^ α - delta) * scale ^ α) <
        (shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale)).toReal := by
      rwa [Real.exp_log hprobPos] at hexp'
    have hmassFinite :
        shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale) ≠ ∞ := ne_of_lt (measure_lt_top Q _)
    apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hmassFinite).mp
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hexp
  filter_upwards [hmass, eventually_gt_atTop (0 : ℝ)] with scale hmassScale hscale
  let lowerOuter : ℝ := (radius / scale) * (d - 1)
  let upperOuter : ℝ := (radius / scale) * (d + 1)
  let endpointLowerOuter : ℝ := (radius / scale) * (d + c)
  let endpointUpperOuter : ℝ := (radius / scale) * (d + b)
  let lowerInner : ℝ := ((radius / scale) * (d + innerLower))
  let upperInner : ℝ := ((radius / scale) * (d + innerUpper))
  have houterLower : radius * (d - 1) / scale = (radius / scale) * (d - 1) := by
    field_simp [ne_of_gt hscale]
  have houterUpper : radius * (d + 1) / scale = (radius / scale) * (d + 1) := by
    field_simp [ne_of_gt hscale]
  have hendpointLower : radius * (d + c) / scale = (radius / scale) * (d + c) := by
    field_simp [ne_of_gt hscale]
  have hendpointUpper : radius * (d + b) / scale = (radius / scale) * (d + b) := by
    field_simp [ne_of_gt hscale]
  have hmapSet : (Skorokhod.scalePath scale) ⁻¹'
      Skorokhod.rangeInOpenIntervalEndsIn
        (radius * (d - 1)) (radius * (d + 1))
        (radius * (d + c)) (radius * (d + b)) =
      Skorokhod.rangeInOpenIntervalEndsIn
        lowerOuter upperOuter endpointLowerOuter endpointUpperOuter := by
    ext path
    change Skorokhod.scalePath scale path ∈
        Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b)) ↔
      path ∈ Skorokhod.rangeInOpenIntervalEndsIn
        lowerOuter upperOuter endpointLowerOuter endpointUpperOuter
    rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_scalePath_iff hscale path]
    dsimp [lowerOuter, upperOuter, endpointLowerOuter, endpointUpperOuter]
    rw [← houterLower, ← houterUpper, ← hendpointLower, ← hendpointUpper]
  have hmapProbability :
      (P.map (Skorokhod.scalePath scale))
        (Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b))) =
        P (Skorokhod.rangeInOpenIntervalEndsIn
          lowerOuter upperOuter endpointLowerOuter endpointUpperOuter) := by
    have hmeas : Measurable (Skorokhod.scalePath scale) :=
      (Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)).measurable
    rw [Measure.map_apply hmeas
      (Skorokhod.measurableSet_rangeInOpenIntervalEndsIn _ _ _ _), hmapSet]
  have hprocessLaw := hEscape.isStableClockProcessLaw.measure_corridorReturnEvent_eq
    hX lowerOuter upperOuter endpointLowerOuter endpointUpperOuter
  have hIocSubset :
      fullSegmentCorridorIocReturnEvent X 0 1
        ((radius / scale) * (d - 1)) ((radius / scale) * (d + 1))
          lowerInner upperInner ⊆
        fullSegmentCorridorReturnEvent X 0 1 lowerOuter upperOuter
          endpointLowerOuter endpointUpperOuter := by
    change segmentCorridorEndpointEvent X 0 1
        lowerOuter upperOuter
        (Set.Ioc lowerInner upperInner) ⊆
      segmentCorridorEndpointEvent X 0 1 lowerOuter upperOuter
        (Set.Ioo endpointLowerOuter endpointUpperOuter)
    apply segmentCorridorEndpointEvent_mono X 0 1 le_rfl le_rfl
    intro x hx
    simp only [Set.mem_Ioc, Set.mem_Ioo] at hx ⊢
    constructor
    · have hfactor : 0 < radius / scale := div_pos hradius hscale
      have hlow : endpointLowerOuter < lowerInner := by
        dsimp [endpointLowerOuter, lowerInner]
        apply mul_lt_mul_of_pos_left _ hfactor
        linarith
      exact lt_trans hlow hx.1
    · have hfactor : 0 < radius / scale := div_pos hradius hscale
      have hupp : upperInner < endpointUpperOuter := by
        dsimp [upperInner, endpointUpperOuter]
        apply mul_lt_mul_of_pos_left _ hfactor
        linarith
      exact lt_of_le_of_lt hx.2 hupp
  have hIocEq :
        shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale) =
        Q (fullSegmentCorridorIocReturnEvent X 0 1
          lowerOuter upperOuter
          lowerInner upperInner) := by
    simp [shiftedEndpointCorridorProbability, lowerOuter, upperOuter,
      lowerInner, upperInner,
      fullSegmentCorridorIocReturnEvent, segmentCorridorEndpointEvent]
  calc
    ENNReal.ofReal (Real.exp ((C / radius ^ α - delta) * scale ^ α)) <
        shiftedEndpointCorridorProbability Q X d innerLower innerUpper
          (radius / scale) := hmassScale
    _ = Q (fullSegmentCorridorIocReturnEvent X 0 1
        ((radius / scale) * (d - 1)) ((radius / scale) * (d + 1))
        lowerInner upperInner) := hIocEq
    _ ≤ Q (fullSegmentCorridorReturnEvent X 0 1 lowerOuter upperOuter
        endpointLowerOuter endpointUpperOuter) :=
      measure_mono hIocSubset
    _ = P (Skorokhod.rangeInOpenIntervalEndsIn
        lowerOuter upperOuter endpointLowerOuter endpointUpperOuter) :=
      hprocessLaw.symm
    _ = (P.map (Skorokhod.scalePath scale))
        (Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (d - 1)) (radius * (d + 1))
          (radius * (d + c)) (radius * (d + b))) := hmapProbability.symm

/-- A finite family of endpoint bands strictly inside a shifted open
interval has the sharp stable escape lower rate. The exponent depends only on
the half-width of the interval; the center and the endpoint bands affect only
the finite positive prefactors. -/
theorem eventually_scaledStableIntervalEndpointBandsProbability_ge_exp
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper epsilon delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper) :
    ∀ᶠ scale : ℝ in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower) / 2) ^ α) - delta) * scale ^ α)) <
          (P.map (Skorokhod.scalePath scale))
            (Skorokhod.rangeInOpenIntervalEndsIn lower upper
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
  let radius : ℝ := (upper - lower) / 2
  let centerRatio : ℝ := (upper + lower) / (upper - lower)
  let c (i : ℤ) : ℝ := (((i : ℝ) - 1) * epsilon) / radius - centerRatio
  let b (i : ℤ) : ℝ := (((i : ℝ) + 1) * epsilon) / radius - centerRatio
  have hwidth : 0 < upper - lower := sub_pos.mpr (lt_trans hlower hupper)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hlowerRatio : lower / radius = centerRatio - 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hupperRatio : upper / radius = centerRatio + 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hcenter : -1 < centerRatio ∧ centerRatio < 1 := by
    constructor
    · have hpos : 0 < upper / radius := div_pos hupper hradius
      rw [hupperRatio] at hpos
      linarith
    · have hneg : lower / radius < 0 := div_neg_of_neg_of_pos hlower hradius
      rw [hlowerRatio] at hneg
      linarith
  have hleft : radius * (centerRatio - 1) = lower := by
    rw [← hlowerRatio]
    field_simp [hradius.ne']
  have hright : radius * (centerRatio + 1) = upper := by
    rw [← hupperRatio]
    field_simp [hradius.ne']
  apply (Finset.Icc (-3 : ℤ) 3).eventually_all.2
  intro i hi
  let lowerEndpoint : ℝ := ((i : ℝ) - 1) * epsilon
  let upperEndpoint : ℝ := ((i : ℝ) + 1) * epsilon
  have hlowerEndpoint : lower < lowerEndpoint := hbands i hi |>.1
  have hupperEndpoint : upperEndpoint < upper := hbands i hi |>.2
  have hc : -1 < c i := by
    dsimp [c, lowerEndpoint]
    have hdiv := div_lt_div_of_pos_right hlowerEndpoint hradius
    rw [hlowerRatio] at hdiv
    linarith
  have hb : b i < 1 := by
    dsimp [b, upperEndpoint]
    have hdiv := div_lt_div_of_pos_right hupperEndpoint hradius
    rw [hupperRatio] at hdiv
    linarith
  have hcb : c i < b i := by
    dsimp [c, b]
    have hendpoint : lowerEndpoint < upperEndpoint := by
      dsimp [lowerEndpoint, upperEndpoint]
      nlinarith [hepsilon]
    have hdiv := div_lt_div_of_pos_right hendpoint hradius
    linarith
  have hendpointLower : radius * (centerRatio + c i) = lowerEndpoint := by
    dsimp [c, lowerEndpoint]
    field_simp [hradius.ne']
    ring
  have hendpointUpper : radius * (centerRatio + b i) = upperEndpoint := by
    dsimp [b, upperEndpoint]
    field_simp [hradius.ne']
    ring
  have hmass := eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hradius hdelta hcenter hc hcb hb
  filter_upwards [hmass] with scale hmassScale
  have hparams :
      Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (centerRatio - 1)) (radius * (centerRatio + 1))
          (radius * (centerRatio + c i)) (radius * (centerRatio + b i)) =
        Skorokhod.rangeInOpenIntervalEndsIn lower upper
          lowerEndpoint upperEndpoint := by
    rw [hleft, hright, hendpointLower, hendpointUpper]
  rw [hparams] at hmassScale
  simpa [radius] using hmassScale


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
