/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Path.PathClass.StepCorridor.Probability.StableRate
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy

/-!
# The fixed constant-corridor input to the stable rate theorem

The public result is
`ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.exists_constantCorridor_rate`.
For a stable path law `P`, stable process `X`, exponent `α > 0`, and fixed
`lower < 0 < upper`, it proves positivity of the scaled-corridor probability
near zero and
`log (P (scaledConstantCorridorEvent a lower upper)).toReal / (-a ^ (-α))`
tends to `κ` times the `M₂` energy of the constant-bound corridor, for some
`κ > 0`. The event is the existing `scaledConstantCorridorEvent`; this module
does not introduce a second path-preimage encoding. This is a concrete
constant-corridor rate, not the uniform rate over all `M₂` corridors required
by the process theorem.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor Set
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

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
        (scaledConstantCorridorEvent a lower upper) P) ∧
      (∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
        0 < (P (scaledConstantCorridorEvent a lower upper)).toReal) ∧
      Tendsto
        (fun a : ℝ => Real.log
          ((P (scaledConstantCorridorEvent a lower upper)).toReal) /
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
      NullMeasurableSet (scaledConstantCorridorEvent a lower upper) P := by
    intro a
    by_cases ha : 0 < a
    · exact nullMeasurableSet_scaledConstantCorridorEvent ha hlower hupper P
    · have hEmpty : scaledConstantCorridorEvent a lower upper = ∅ := by
        ext f
        constructor
        · rintro ⟨hstart, hpath⟩
          have h := (hpath ⊥).1
          rw [hstart] at h
          have ha' : a ≤ 0 := le_of_not_gt ha
          have hscale : 0 ≤ a * lower :=
            mul_nonneg_of_nonpos_of_nonpos ha' hlower.le
          linarith
        · simp
      rw [hEmpty]
      exact nullMeasurableSet_empty
  have hnull : ∀ᶠ a : ℝ in l,
      0 < (P (scaledConstantCorridorEvent a lower upper)).toReal := by
    have hradius : 0 < (upper - lower) / 2 := by linarith
    have hlimneg : (1 / ((upper - lower) / 2)) ^ α * C < 0 :=
      mul_neg_of_pos_of_neg
        (Real.rpow_pos_of_pos (one_div_pos.mpr hradius) α) hC
    have hevent := hscaled.eventually (Iio_mem_nhds hlimneg)
    filter_upwards [hevent, self_mem_nhdsWithin] with a hnegative ha
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
    exact hrealpos
  have hrate : Tendsto
      (fun a : ℝ => Real.log
        ((P (scaledConstantCorridorEvent a lower upper)).toReal) /
          (-(a ^ (-α)))) l
      (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
    have hnegativeRate : Tendsto
        (fun a : ℝ => -(a ^ α * Real.log
          ((P (scaledConstantCorridorEvent a lower upper)).toReal))) l
        (𝓝 (-((1 / ((upper - lower) / 2)) ^ α * C))) := hscaled.neg
    have hratioEq : (fun a : ℝ => Real.log
        ((P (scaledConstantCorridorEvent a lower upper)).toReal) /
          (-(a ^ (-α)))) =ᶠ[l]
        (fun a : ℝ => -(a ^ α * Real.log
          ((P (scaledConstantCorridorEvent a lower upper)).toReal))) := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have hpow : a ^ (-α) = (a ^ α)⁻¹ := Real.rpow_neg ha.le α
      have hpowne : a ^ α ≠ 0 := (Real.rpow_pos_of_pos ha α).ne'
      rw [hpow]
      field_simp [hpowne]
    have hratio := Filter.Tendsto.congr' hratioEq.symm hnegativeRate
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
