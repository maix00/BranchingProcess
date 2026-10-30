/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Order-monotone observables of measure-preserving maps

## Public declarations

* `ProbabilityTheory.ae_eq_comp_of_le_comp`: if `T` preserves a finite measure, `F : X → ℝ`
  is a.e. measurable, and `F ≤ F ∘ T` almost everywhere, then `F ∘ T = F` almost everywhere.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **Invariance from monotonicity under a measure-preserving map.** If `F` is a.e. measurable,
`T` preserves a finite measure, and `F x ≤ F (T x)` almost everywhere, then `F ∘ T =ᵐ[μ] F`.
For each rational `c`, the upper level set `{x | c ≤ F x}` is almost contained in its preimage
under `T`; measure preservation and finiteness give equality almost everywhere. The rational
level sets determine `F` almost everywhere. -/
theorem ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {F : X → ℝ} (hF : AEMeasurable F μ)
    (hle : ∀ᵐ x ∂μ, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F := by
  set F0 : X → ℝ := hF.mk F with hF0def
  have hF0m : Measurable F0 := hF.measurable_mk
  have hFF0 : F =ᵐ[μ] F0 := hF.ae_eq_mk
  have hkey : ∀ c : ℚ, T ⁻¹' {x | (c : ℝ) ≤ F x} =ᵐ[μ] {x | (c : ℝ) ≤ F x} := by
    intro c
    set s : Set X := {x | (c : ℝ) ≤ F x} with hs
    have hsmeas : NullMeasurableSet s μ := by
      have hseq : s =ᵐ[μ] {x | (c : ℝ) ≤ F0 x} := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [hFF0] with x hx
        simp only [hs, Set.mem_ofPred_eq, hx]
      exact (measurableSet_le measurable_const hF0m).nullMeasurableSet.congr hseq.symm
    have hsub : s ≤ᵐ[μ] T ⁻¹' s := by
      filter_upwards [hle] with x hx hxs
      exact le_trans hxs hx
    have hmeq : μ (T ⁻¹' s) = μ s := hT.measure_preimage hsmeas
    have : s =ᵐ[μ] T ⁻¹' s :=
      ae_eq_of_ae_subset_of_measure_ge hsub (le_of_eq hmeq) hsmeas (measure_ne_top μ _)
    exact this.symm
  have hall : ∀ᵐ x ∂μ, ∀ c : ℚ,
      (x ∈ T ⁻¹' {x | (c : ℝ) ≤ F x}) ↔ (x ∈ {x | (c : ℝ) ≤ F x}) := by
    rw [ae_all_iff]
    intro c
    exact Filter.eventuallyEqSet_iff.1 (hkey c)
  filter_upwards [hall] with x hx
  change F (T x) = F x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hlt
    have h := (hx c).symm
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
    exact absurd (h.1 hc2.le) (not_le.2 hc1)
  · obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn hgt
    have h := hx c
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h
    exact absurd (h.1 hc2.le) (not_le.2 hc1)

end ProbabilityTheory
