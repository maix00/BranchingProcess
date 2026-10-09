/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Path.PathClass.StepCorridor.Probability.StableRate
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
import Topology.Cadlag.Skorokhod.Scaling

/-!
# The fixed constant-corridor input to the stable rate theorem

The stable path-law rate for a constant `M₂` corridor supplies the complete
probability input for that fixed corridor after the path is scaled by `a⁻¹`.
This is a concrete component rate, not a claim of the uniform rate over all
`M₂` corridors required by the process theorem.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor Set
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- Pull back a fixed constant corridor along spatial rescaling by `a⁻¹`.
The parameter `a` is the small corridor width. -/
def scaledPathConstantCorridorEvent (a lower upper : ℝ)
    (hlower : lower < 0) (hupper : 0 < upper) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | Skorokhod.scalePath a⁻¹ f ∈
    (ContinuousAdmissibleStepCorridor.constantBounds hlower hupper).toSet}

/-- The scaled-path event is exactly the source's pointwise-strict corridor
with boundaries multiplied by `a`, for positive `a`. -/
theorem scaledPathConstantCorridorEvent_eq
    {a lower upper : ℝ} (ha : 0 < a)
    (hlower : lower < 0) (hupper : 0 < upper) :
    scaledPathConstantCorridorEvent a lower upper hlower hupper =
      scaledConstantCorridorEvent a lower upper := by
  ext f
  simp only [scaledPathConstantCorridorEvent,
    ContinuousAdmissibleStepCorridor.constantBounds_toSet hlower hupper,
    scaledConstantCorridorEvent, constantCorridorEvent,
    Set.mem_ofPred_eq, Skorokhod.scalePath_apply]
  constructor
  · rintro ⟨hstart, hpath⟩
    refine ⟨?_, ?_⟩
    · exact Or.resolve_left (mul_eq_zero.mp hstart) (inv_ne_zero ha.ne')
    · intro t
      refine ⟨?_, ?_⟩
      · have hinv : a * (a⁻¹ * f t) = f t := by
          field_simp
        have hm := mul_lt_mul_of_pos_left (hpath t).1 ha
        rw [hinv] at hm
        exact hm
      · have hinv : a * (a⁻¹ * f t) = f t := by
          field_simp
        have hm := mul_lt_mul_of_pos_left (hpath t).2 ha
        rw [hinv] at hm
        exact hm
  · rintro ⟨hstart, hpath⟩
    refine ⟨?_, ?_⟩
    · rw [hstart]
      simp
    · intro t
      refine ⟨?_, ?_⟩
      · have hinv : a * (a⁻¹ * f t) = f t := by
          field_simp
        apply lt_of_mul_lt_mul_left _ ha.le
        rw [hinv]
        exact (hpath t).1
      · have hinv : a * (a⁻¹ * f t) = f t := by
          field_simp
        apply lt_of_mul_lt_mul_left _ ha.le
        rw [hinv]
        exact (hpath t).2

/-- For one fixed constant admissible corridor, the logarithmic probability
has a negative-power rate with the exact `M₂` energy. Positivity and
null-measurability are proved as part of the package; no probability-rate
limit is assumed. -/
theorem exists_constantCorridor_rate
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα : 0 < α)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun a : ℝ => -(a ^ (-α))) (𝓝[>] (0 : ℝ)) atBot ∧
      (∀ a : ℝ, NullMeasurableSet
        (scaledPathConstantCorridorEvent a lower upper hlower hupper) P) ∧
      (∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
        0 < (P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal) ∧
      Tendsto
        (fun a : ℝ => Real.log
          ((P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal) /
            (-(a ^ (-α))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α
          (ContinuousAdmissibleStepCorridor.constantBounds hlower hupper)).toReal)) := by
  obtain ⟨C, hC, hscaled⟩ :=
    exists_tendsto_log_scaledConstantCorridorEvent hP hX hcdf hlower hupper
  let κ : ℝ := -((2 : ℝ) ^ α * C)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α) hC)
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hrpow : Tendsto (fun a : ℝ => a ^ (-α)) l atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hα)
  have hg : Tendsto (fun a : ℝ => -(a ^ (-α))) l atBot := by
    exact tendsto_neg_atTop_atBot.comp hrpow
  let c : ContinuousAdmissibleStepCorridor := ContinuousAdmissibleStepCorridor.constantBounds hlower hupper
  have hmeas : ∀ a : ℝ,
      NullMeasurableSet (scaledPathConstantCorridorEvent a lower upper hlower hupper) P := by
    intro a
    apply ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable c P
    have hcontinuous : Continuous
        (fun f : CadlagPath unitInterval ℝ => Skorokhod.scalePath (a⁻¹) f) := by
      exact Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)
    exact hcontinuous.measurable.aemeasurable
  have hnull : ∀ᶠ a : ℝ in l,
      0 < (P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal := by
    have hradius : 0 < (upper - lower) / 2 := by linarith
    have hlimneg : (1 / ((upper - lower) / 2)) ^ α * C < 0 :=
      mul_neg_of_pos_of_neg
        (Real.rpow_pos_of_pos (one_div_pos.mpr hradius) α) hC
    have hevent := hscaled.eventually (Iio_mem_nhds hlimneg)
    filter_upwards [hevent, self_mem_nhdsWithin] with a hnegative ha
    have hevent' := hnegative
    have hpowpos : 0 < a ^ α := Real.rpow_pos_of_pos ha α
    have hlogneg : Real.log
        ((P (scaledConstantCorridorEvent a lower upper)).toReal) < 0 := by
      by_contra hnot
      have hlognonneg : 0 ≤ Real.log
          ((P (scaledConstantCorridorEvent a lower upper)).toReal) := not_lt.mp hnot
      have hprodnonneg := mul_nonneg hpowpos.le hlognonneg
      linarith
    have hrealpos : 0 < (P
        (scaledConstantCorridorEvent a lower upper)).toReal := by
      have hnonneg : 0 ≤ (P (scaledConstantCorridorEvent a lower upper)).toReal :=
        ENNReal.toReal_nonneg
      by_contra hnot
      have hzero : (P (scaledConstantCorridorEvent a lower upper)).toReal = 0 :=
        le_antisymm (not_lt.mp hnot) hnonneg
      rw [hzero, Real.log_zero] at hlogneg
      exact (lt_irrefl 0) hlogneg
    rw [scaledPathConstantCorridorEvent_eq ha hlower hupper]
    exact hrealpos
  have hrate : Tendsto
      (fun a : ℝ => Real.log
        ((P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal) /
          (-(a ^ (-α)))) l
      (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
    have hnegativeRate : Tendsto
        (fun a : ℝ => -(a ^ α * Real.log
          ((P (scaledConstantCorridorEvent a lower upper)).toReal))) l
        (𝓝 (-((1 / ((upper - lower) / 2)) ^ α * C))) := hscaled.neg
    have hnegativeRate' : Tendsto
        (fun a : ℝ => -(a ^ α * Real.log
          ((P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal))) l
        (𝓝 (-((1 / ((upper - lower) / 2)) ^ α * C))) := by
      apply hnegativeRate.congr'
      filter_upwards [self_mem_nhdsWithin] with a ha
      rw [scaledPathConstantCorridorEvent_eq ha hlower hupper]
    have hratioEq : (fun a : ℝ => Real.log
        ((P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal) /
          (-(a ^ (-α)))) =ᶠ[l]
        (fun a : ℝ => -(a ^ α * Real.log
          ((P (scaledPathConstantCorridorEvent a lower upper hlower hupper)).toReal))) := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have hpow : a ^ (-α) = (a ^ α)⁻¹ := Real.rpow_neg ha.le α
      have hpowne : a ^ α ≠ 0 := (Real.rpow_pos_of_pos ha α).ne'
      rw [hpow]
      field_simp [hpowne]
    have hratio := Filter.Tendsto.congr' hratioEq.symm hnegativeRate'
    have hwidth : 0 < upper - lower := by linarith
    have hradius : 0 < (upper - lower) / 2 := by linarith
    have hdiv : 1 / ((upper - lower) / 2) = 2 / (upper - lower) := by
      field_simp [ne_of_gt hwidth]
    have hfactor : (1 / ((upper - lower) / 2)) ^ α =
        (2 : ℝ) ^ α * (upper - lower) ^ (-α) := by
      rw [hdiv, Real.div_rpow (by norm_num) hwidth.le,
        Real.rpow_neg hwidth.le α]
      ring
    have henergy : (ContinuousAdmissibleStepCorridor.energy α c).toReal = (upper - lower) ^ (-α) := by
      have hu : ∀ t, c.upper.eval t = (upper : EReal) := by
        intro t
        simp [c, ContinuousAdmissibleStepCorridor.constantBounds, StepBoundary.eval_constant]
      have hl : ∀ t, c.lower.eval t = (lower : EReal) := by
        intro t
        simp [c, ContinuousAdmissibleStepCorridor.constantBounds, StepBoundary.eval_constant]
      rw [ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values α c _ _ hu hl,
        widthCost_coe_sub α upper lower hwidth]
      simp [Real.rpow_nonneg (le_of_lt hwidth) (-α)]
    have htarget : -((2 / (upper - lower)) ^ α * C) =
        κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal := by
      rw [← hdiv, hfactor, henergy]
      dsimp [κ]
      ring
    simpa [l, c, htarget] using hratio
  exact ⟨κ, hκ, by simpa [l] using hg, hmeas, hnull, by simpa [l, c] using hrate⟩

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
