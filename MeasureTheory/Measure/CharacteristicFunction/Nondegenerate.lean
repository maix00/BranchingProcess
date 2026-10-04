/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Characteristic functions and point masses

This file records a criterion, independent of any distribution family, for a
probability measure on the real line to be a point mass.
-/

@[expose] public section

namespace MeasureTheory

open MeasureTheory.Measure
open scoped MeasureTheory

/-- If a probability measure has characteristic function of norm one at every
frequency, then it is a Dirac measure. -/
theorem exists_dirac_of_norm_charFun_eq_one {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hφ : ∀ t : ℝ, ‖charFun μ t‖ = 1) :
    ∃ x : ℝ, μ = Measure.dirac x := by
  let δ : Measure ℝ := (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)
  have hδ : δ = Measure.dirac 0 := by
    apply Measure.ext_of_charFun
    ext t
    have hconv : μ ∗ μ.map Neg.neg = δ := by
      have hprod : μ.prod (μ.map Neg.neg) =
          (μ.prod μ).map (Prod.map id Neg.neg) := by
        simpa only [Measure.map_id] using
          (Measure.map_prod_map μ μ measurable_id measurable_neg)
      rw [Measure.conv, hprod, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    have hneg : charFun (μ.map Neg.neg) t = charFun μ (-t) := by
      simpa using (charFun_map_mul (μ := μ) (-1) t)
    rw [← hconv, charFun_conv, hneg, charFun_neg]
    calc
      charFun μ t * star (charFun μ t) =
          (Complex.normSq (charFun μ t) : ℂ) := by
            rw [← starRingEnd_apply]
            simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj (charFun μ t)
      _ = (‖charFun μ t‖ ^ 2 : ℝ) := by rw [Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [hφ t]; norm_num
      _ = charFun (Measure.dirac 0) t := by simp [charFun_dirac]
  have hdiag : μ.prod μ {p : ℝ × ℝ | p.1 = p.2} = 1 := by
    have hzero : δ {0} = 1 := by rw [hδ]; simp
    change (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2) {0} = 1 at hzero
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at hzero
    have hset : (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' ({0} : Set ℝ) =
        {p | p.1 = p.2} := by
      ext p
      simp [sub_eq_zero]
    rw [hset] at hzero
    exact hzero
  have hrect (s : Set ℝ) (hs : MeasurableSet s) : μ s = 0 ∨ μ s = 1 := by
    have hzero : μ.prod μ (s ×ˢ sᶜ) = 0 := by
      have hdiagCompl : μ.prod μ {p : ℝ × ℝ | p.1 = p.2}ᶜ = 0 := by
        rw [measure_compl (measurableSet_eq_fun measurable_fst measurable_snd)
          (measure_ne_top _ _), hdiag]
        simp
      have hsubset : s ×ˢ sᶜ ⊆ {p : ℝ × ℝ | p.1 = p.2}ᶜ := by
        intro p hp hpeq
        exact hp.2 (hpeq ▸ hp.1)
      have hle : (μ.prod μ) (s ×ˢ sᶜ) ≤
          (μ.prod μ) {p : ℝ × ℝ | p.1 = p.2}ᶜ :=
        MeasureTheory.measure_mono hsubset
      rw [hdiagCompl] at hle
      exact le_antisymm hle bot_le
    have hprod : μ s * μ sᶜ = 0 := by simpa only [Measure.prod_prod] using hzero
    rcases mul_eq_zero.mp hprod with hs0 | hsc0
    · exact Or.inl hs0
    · right
      have hadd : μ s + μ sᶜ = μ Set.univ :=
        @MeasureTheory.measure_add_measure_compl ℝ _ μ s hs
      rw [measure_univ] at hadd
      rw [hsc0] at hadd
      simpa using hadd
  have hzeroOne : IsZeroOneMeasure μ := ⟨fun {s} hs => hrect s hs⟩
  have hneZero : NeZero μ := ⟨by
    intro hzero
    have hμ : μ Set.univ = 1 := measure_univ
    rw [hzero] at hμ
    simp at hμ⟩
  exact @IsZeroOneMeasure.exists_eq_dirac ℝ _ μ hzeroOne inferInstance hneZero

end MeasureTheory

end
