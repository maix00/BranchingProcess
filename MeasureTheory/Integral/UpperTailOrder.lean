/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Integral order from upper-tail probabilities

## Public declarations

* `integral_le_of_measure_ge_le`: for integrable real observables on probability
  spaces, $P(f\ge x)\le Q(g\ge x)$ for every real $x$ implies
  $\int f\,dP\le\int g\,dQ$.
-/

open Filter Set
open scoped ENNReal

namespace MeasureTheory

private theorem integral_nonneg_le_of_tail_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {f : Ω → ℝ} {g : Ω' → ℝ}
    (hf : Integrable f P) (hg : Integrable g Q)
    (hf₀ : ∀ ω, 0 ≤ f ω) (hg₀ : ∀ ω, 0 ≤ g ω)
    (h : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), P {ω | x ≤ f ω} ≤ Q {ω | x ≤ g ω}) :
    (∫ ω, f ω ∂P) ≤ ∫ ω, g ω ∂Q := by
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hf₀) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hg₀) hg.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hg).ne ?_
  rw [lintegral_eq_lintegral_meas_le P (.of_forall hf₀) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le Q (.of_forall hg₀) hg.aemeasurable]
  exact lintegral_mono_ae h

/-- Upper-tail stochastic order implies order of the means by the layer-cake
formula applied to the positive and negative parts. -/
public theorem integral_le_of_measure_ge_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {f : Ω → ℝ} {g : Ω' → ℝ}
    (hf : Integrable f P) (hg : Integrable g Q) (hfm : Measurable f) (hgm : Measurable g)
    (h : ∀ x : ℝ, P {ω | x ≤ f ω} ≤ Q {ω | x ≤ g ω}) :
    (∫ ω, f ω ∂P) ≤ ∫ ω, g ω ∂Q := by
  let fp := fun ω => max (f ω) 0
  let fm := fun ω => max (-f ω) 0
  let gp := fun ω => max (g ω) 0
  let gm := fun ω => max (-g ω) 0
  have hfp : Integrable fp P := hf.real_toNNReal
  have hfm' : Integrable fm P := hf.neg.real_toNNReal
  have hgp : Integrable gp Q := hg.real_toNNReal
  have hgm' : Integrable gm Q := hg.neg.real_toNNReal
  have hp : (∫ ω, fp ω ∂P) ≤ ∫ ω, gp ω ∂Q := by
    apply integral_nonneg_le_of_tail_le hfp hgp (fun _ => le_max_right ..) (fun _ => le_max_right ..)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    simpa only [fp, gp, le_max_iff, or_iff_left (not_le_of_gt hx)] using h x
  have hm : (∫ ω, gm ω ∂Q) ≤ ∫ ω, fm ω ∂P := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := gm) (.of_forall fun _ => le_max_right ..) hgm'.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (f := fm) (.of_forall fun _ => le_max_right ..) hfm'.aestronglyMeasurable]
    refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hfm').ne ?_
    rw [lintegral_eq_lintegral_meas_lt (f := gm) Q (.of_forall fun _ => le_max_right ..) hgm'.aemeasurable,
      lintegral_eq_lintegral_meas_lt (f := fm) P (.of_forall fun _ => le_max_right ..) hfm'.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    have hgset : {ω | x < gm ω} = {ω | -x ≤ g ω}ᶜ := by
      ext ω
      simp [gm, lt_max_iff, hx.not_gt, lt_neg, not_le]
    have hfset : {ω | x < fm ω} = {ω | -x ≤ f ω}ᶜ := by
      ext ω
      simp [fm, lt_max_iff, hx.not_gt, lt_neg, not_le]
    have hgs : MeasurableSet {ω | -x ≤ g ω} := hgm measurableSet_Ici
    have hfs : MeasurableSet {ω | -x ≤ f ω} := hfm measurableSet_Ici
    rw [hgset, hfset, prob_compl_eq_one_sub hgs, prob_compl_eq_one_sub hfs]
    exact tsub_le_tsub_left (h (-x)) _
  have hf' : f = fun ω => fp ω - fm ω := by
    funext ω
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  have hg' : g = fun ω => gp ω - gm ω := by
    funext ω
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hf', hg', integral_sub hfp hfm', integral_sub hgp hgm']
  exact sub_le_sub hp hm

end MeasureTheory
