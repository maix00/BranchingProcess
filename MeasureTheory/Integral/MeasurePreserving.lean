/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals under measure-preserving maps

## Public declarations

* `MeasureTheory.MeasurePreserving.integral_comp_of_integrable`: if `φ` sends
  `μ` to `ν`, then `∫ x, f (φ x) ∂μ = ∫ y, f y ∂ν` for an integrable
  function with values in a real normed space.
* `MeasureTheory.MeasurePreserving.setIntegral_comp_of_preimage_eq`: if `φ`
  preserves `μ` and `φ ⁻¹' s = s`, then
  `∫ x in s, f (φ x) ∂μ = ∫ x in s, f x ∂μ` for a.e.-strongly measurable `f`.
-/

@[expose] public section

namespace MeasureTheory.MeasurePreserving

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {ν : Measure β} {φ : α → β}

/-- Integrating an integrable function after a measure-preserving map gives the same integral
over the target measure. Unlike `MeasurePreserving.integral_comp`, this statement does not
require the map to be injective. -/
theorem integral_comp_of_integrable (hφ : MeasurePreserving φ μ ν) {f : β → E}
    (hf : Integrable f ν) :
    ∫ x, f (φ x) ∂μ = ∫ y, f y ∂ν := by
  have hfmap : AEStronglyMeasurable f (Measure.map φ μ) := by
    rw [hφ.map_eq]
    exact hf.aestronglyMeasurable
  have hmap := integral_map hφ.aemeasurable (f := f) hfmap
  rw [hφ.map_eq] at hmap
  exact hmap.symm

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {φ : X → X}

/-- A measure-preserving map leaves the integral over an invariant measurable set unchanged
after composition. The map need not be injective. -/
theorem setIntegral_comp_of_preimage_eq (hφ : MeasurePreserving φ μ μ) {f : X → E}
    (hf : AEStronglyMeasurable f μ) {s : Set X} (hs : MeasurableSet s)
    (hpre : φ ⁻¹' s = s) :
    ∫ x in s, f (φ x) ∂μ = ∫ x in s, f x ∂μ := by
  have hmap : Measure.map φ μ = μ := hφ.map_eq
  have hfmap : AEStronglyMeasurable f (Measure.map φ μ) := by rw [hmap]; exact hf
  calc ∫ x in s, f (φ x) ∂μ
      = ∫ x in φ ⁻¹' s, f (φ x) ∂μ := by rw [hpre]
    _ = ∫ y in s, f y ∂Measure.map φ μ :=
      (setIntegral_map hs hfmap hφ.aemeasurable).symm
    _ = ∫ y in s, f y ∂μ := by rw [hmap]

end MeasureTheory.MeasurePreserving
