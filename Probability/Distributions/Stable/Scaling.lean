/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic

/-!
# Positive rescaling of stable laws
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

set_option linter.style.haveILetI false in
/-- A positive spatial rescaling preserves stability and multiplies its
affine shift by the same factor. -/
theorem IsAlphaStable.map_mul
    {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ)
    (r : ℝ) (hr : 0 < r) : IsAlphaStable α (μ.map fun x => r * x) := by
  let f : ℝ → ℝ := fun x => r * x
  let g : ℝ → ℝ := fun x => r⁻¹ * x
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hμ' : IsProbabilityMeasure (μ.map f) := by infer_instance
  refine ⟨h.1, h.2.1, hμ', ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hleft : μ = (μ.map f).map g := by
      have hcomp : g ∘ f = id := by
        funext x
        simp [f, g, hr.ne']
      rw [Measure.map_map hg hf, hcomp]
      simp
    have hright : (μ.map f).map g = Measure.dirac (g y) := by
      rw [hy, Measure.map_dirac' hg]
    exact h.nondegenerate ⟨g y, hleft.trans hright⟩
  · intro a b ha hb
    obtain ⟨shift, hstable⟩ := h.2.2.2.2 a b ha hb
    refine ⟨r * shift, ?_⟩
    calc
      ((μ.map f).prod (μ.map f)).map (weightedSum a b) =
          ((μ.prod μ).map (weightedSum a b)).map f := by
        rw [Measure.map_prod_map μ μ hf hf]
        rw [Measure.map_map (measurable_weightedSum a b) (hf.prodMap hf)]
        rw [Measure.map_map hf (measurable_weightedSum a b)]
        apply Measure.map_congr
        filter_upwards [] with p
        simp [weightedSum, f]
        ring
      _ = (μ.map (affine (alphaStableScale α a b) shift)).map f := by
        rw [hstable]
      _ = (μ.map f).map (affine (alphaStableScale α a b) (r * shift)) := by
        rw [Measure.map_map hf (measurable_affine _ _),
          Measure.map_map (measurable_affine _ _) hf]
        apply Measure.map_congr
        filter_upwards [] with x
        simp [f, affine]
        ring

end ProbabilityTheory

end
