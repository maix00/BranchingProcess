/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Cosine defect of a probability measure

This module owns the basic real-valued cosine defect and its characteristic-
function formulas. It is independent of the Tauberian inversion kernel.
-/

open MeasureTheory
open scoped Complex

@[expose] public section

namespace ProbabilityTheory

/-- The cosine defect of a measure, written as a real integral. -/
noncomputable def cosineDefectIntegral (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ y, 1 - Real.cos (t * y) ∂μ

/-- For a probability measure, the integral cosine defect is the real-part
defect of its characteristic function. -/
theorem cosineDefectIntegral_eq_one_sub_charFun_re
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cosineDefectIntegral μ t = 1 - (charFun μ t).re := by
  let f : ℝ → ℂ := fun y => Complex.exp (t * y * Complex.I)
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun y => ?_)
    simp [f, Complex.norm_exp]
  have hcosInt : Integrable (fun y : ℝ => Real.cos (t * y)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hcos : (∫ y : ℝ, Real.cos (t * y) ∂μ) = (charFun μ t).re := by
    rw [charFun_apply_real]
    calc
      (∫ y : ℝ, Real.cos (t * y) ∂μ) = ∫ y : ℝ, (f y).re ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [f]
        simp [Complex.exp_re]
      _ = (∫ y : ℝ, f y ∂μ).re := integral_re hf
  have hconst : (∫ _y : ℝ, (1 : ℝ) ∂μ) = 1 := by
    simp [Measure.real_def]
  rw [cosineDefectIntegral, integral_sub (integrable_const (1 : ℝ)) hcosInt,
    hconst, hcos]

/-- The cosine defect is a continuous function of frequency for a probability
measure. This follows from the standard continuity theorem for
characteristic functions. -/
theorem continuous_cosineDefectIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Continuous (cosineDefectIntegral μ) := by
  have hchar : Continuous (fun t : ℝ => (charFun μ t).re) :=
    Complex.continuous_re.comp continuous_charFun
  have hEq : cosineDefectIntegral μ =
      fun t => 1 - (charFun μ t).re := by
    funext t
    exact cosineDefectIntegral_eq_one_sub_charFun_re μ t
  rw [hEq]
  exact continuous_const.sub hchar

/-- The cosine defect of a probability measure lies between zero and two. -/
theorem cosineDefectIntegral_mem_Icc
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cosineDefectIntegral μ t ∈ Set.Icc 0 2 := by
  let f : ℝ → ℝ := fun y => 1 - Real.cos (t * y)
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun y => ?_)
    dsimp [f]
    rw [abs_le]
    constructor <;> have hlow := Real.neg_one_le_cos (t * y) <;>
      have hupp := Real.cos_le_one (t * y) <;> linarith
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [] with y
    dsimp [f]
    linarith [Real.cos_le_one (t * y)]
  have hupper : f ≤ᵐ[μ] fun _ : ℝ => 2 := by
    filter_upwards [] with y
    dsimp [f]
    linarith [Real.neg_one_le_cos (t * y)]
  constructor
  · exact integral_nonneg_of_ae hnonneg
  · have hmono := integral_mono_ae hf (integrable_const (2 : ℝ)) hupper
    simpa [cosineDefectIntegral, f] using hmono

end ProbabilityTheory

end
