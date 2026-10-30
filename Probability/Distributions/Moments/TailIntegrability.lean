/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Integral.Basic

import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Integrability from two-sided tails

This module records reusable criteria for integrability of real random
variables from the integrated tail of their absolute value.

The regularly varying case applies the tail-integral form of Karamata's theorem
from `Analysis.Asymptotics.RegularVariation.Integral.Basic`, which cites Bingham,
Goldie, and Teugels, *Regular Variation*, Theorem 1.5.11(ii).

## Public declarations

- `integrableOn_twoSidedTail_of_integrable_abs`: if `∫|x| μ(dx)<∞`, then
  `t ↦ μ(|x|>t)` is integrable on each upper ray.
- `integrable_id_of_integrableOn_twoSidedTail`: for a finite measure, an
  integrable two-sided tail on `(0,∞)` implies `Integrable id μ`.
- `integrable_id_of_twoSidedTail_regularlyVarying`: for a finite measure, a regularly varying
  two-sided tail of index `-α` with `α>1` implies `Integrable id μ`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory

/-- A finite first absolute moment makes the two-sided tail integrable over
every upper ray. This is the layer-cake identity in `ℝ≥0∞`, followed by
`integrable_toReal_of_lintegral_ne_top` from Mathlib. -/
theorem integrableOn_twoSidedTail_of_integrable_abs
    (μ : Measure ℝ)
    (habsolute : Integrable (fun x : ℝ => |x|) μ) {radius : ℝ}
    (hradius : 0 ≤ radius) :
    IntegrableOn (fun t : ℝ => μ.real {x : ℝ | t < |x|}) (Ioi radius) volume := by
  let tail : ℝ → ℝ≥0∞ := fun t => μ {x : ℝ | t < |x|}
  have htailMeas : Measurable tail := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono fun _ hx => lt_of_le_of_lt hab hx
  have hlayer : (∫⁻ x, ENNReal.ofReal |x| ∂μ) = ∫⁻ t in Ioi (0 : ℝ), tail t :=
    lintegral_eq_lintegral_meas_lt μ
      (ae_of_all μ fun x => abs_nonneg x) continuous_abs.measurable.aemeasurable
  have htailFinite : (∫⁻ t in Ioi (0 : ℝ), tail t) < ∞ := by
    rw [← hlayer]
    exact Integrable.lintegral_lt_top habsolute
  have htailRealIntegrable : Integrable (fun t : ℝ => (tail t).toReal)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_toReal_of_lintegral_ne_top htailMeas.aemeasurable htailFinite.ne
  have htailEq : (fun t : ℝ => (tail t).toReal) =
      (fun t => μ.real {x : ℝ | t < |x|}) := by
    funext t
    rfl
  rw [← htailEq]
  change IntegrableOn (fun t : ℝ => (tail t).toReal) (Ioi (0 : ℝ)) volume at htailRealIntegrable
  exact htailRealIntegrable.mono_set (Ioi_subset_Ioi hradius)

/-- If the two-sided tail is integrable on the positive half-line, then the
law has a finite first absolute moment. This is the converse layer-cake
direction and does not require any regular-variation assumption. -/
theorem integrable_id_of_integrableOn_twoSidedTail
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (htail : IntegrableOn (fun t : ℝ => μ.real {x : ℝ | t < |x|})
      (Ioi (0 : ℝ)) volume) :
    Integrable (id : ℝ → ℝ) μ := by
  let tail : ℝ → ℝ := fun t => μ.real {x : ℝ | t < |x|}
  have htailAntitone : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := μ)
    · intro x hx
      exact lt_of_le_of_lt hab hx
  have htailMeasurable : Measurable tail := htailAntitone.measurable
  have htailNonneg (t : ℝ) : 0 ≤ tail t := measureReal_nonneg
  have htailReal : Integrable tail (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [tail, IntegrableOn] using htail
  have htailRealLIntegralNeTop :
      (∫⁻ t, ENNReal.ofReal (tail t)
        ∂(volume.restrict (Ioi (0 : ℝ)))) ≠ ∞ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      htailReal.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => htailNonneg t)).2 htailReal
  have htailRealLIntegralFinite :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tail t) ∂volume) < ∞ := by
    exact lt_top_iff_ne_top.mpr (by simpa using htailRealLIntegralNeTop)
  let tailENN : ℝ → ℝ≥0∞ := fun t => μ {x : ℝ | t < |x|}
  have htailENN_eq (t : ℝ) : tailENN t = ENNReal.ofReal (tail t) := by
    dsimp [tailENN, tail]
    rw [Measure.real]
    exact (ENNReal.ofReal_toReal (measure_lt_top μ _).ne).symm
  have htailENNFinite :
      (∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume) < ∞ := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume) =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tail t) ∂volume := by
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall htailENN_eq
      _ < ∞ := htailRealLIntegralFinite
  have hlayercake :
      (∫⁻ x, ENNReal.ofReal |x| ∂μ) =
        ∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume :=
    lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun x => abs_nonneg x)
      continuous_abs.measurable.aemeasurable
  have habsoluteLIntegralNeTop :
      (∫⁻ x, ENNReal.ofReal |x| ∂μ) ≠ ∞ := by
    rw [hlayercake]
    exact htailENNFinite.ne
  have habsolute : Integrable (fun x : ℝ => |x|) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      continuous_abs.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => abs_nonneg x)).1
      habsoluteLIntegralNeTop
  have habsoluteNorm : Integrable (fun x : ℝ => ‖x‖) μ := by
    simpa [Real.norm_eq_abs] using habsolute
  exact (integrable_norm_iff (f := id) measurable_id.aestronglyMeasurable).1
    habsoluteNorm

/-- A finite measure with a regularly varying two-sided tail of index
`-α`, for `α > 1`, has an integrable identity function. -/
theorem integrable_id_of_twoSidedTail_regularlyVarying
    {ν : Measure ℝ} [IsFiniteMeasure ν] {α : ℝ}
    (hα : 1 < α)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Integrable (id : ℝ → ℝ) ν := by
  let tail : ℝ → ℝ := fun t => ν.real {x : ℝ | t < |x|}
  have hanti : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := ν)
      (fun x hx => lt_of_le_of_lt hab hx) (by finiteness)
  have hnonneg (t : ℝ) : 0 ≤ tail t := measureReal_nonneg
  have hKaramata := htail.tendsto_integral_Ioi_div_mul_of_antitone
    hα hanti hnonneg
  have hlimitPos : 0 < 1 / (α - 1) := by positivity
  have hratioPos : ∀ᶠ R : ℝ in atTop,
      0 < (∫ t in Ioi R, tail t) / (R * tail R) :=
    hKaramata.eventually (isOpen_Ioi.mem_nhds hlimitPos)
  obtain ⟨Rratio, hRratio⟩ := eventually_atTop.1 hratioPos
  obtain ⟨Rtail, hRtail⟩ := eventually_atTop.1 htail.eventually_pos
  let R : ℝ := max 1 (max Rratio Rtail)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRratioBound : Rratio ≤ R := by
    dsimp [R]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRtailBound : Rtail ≤ R := by
    dsimp [R]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have htailR : 0 < tail R := hRtail R hRtailBound
  have hratioR : 0 < (∫ t in Ioi R, tail t) / (R * tail R) :=
    hRratio R hRratioBound
  have htailIntegrable : IntegrableOn tail (Ioi R) volume := by
    by_contra hnot
    have hzero : (∫ t in Ioi R, tail t) = 0 := integral_undef hnot
    rw [hzero, zero_div] at hratioR
    exact (lt_irrefl 0) hratioR
  have htailMeasurable : Measurable tail := hanti.measurable
  have htailLeTotal (t : ℝ) : tail t ≤ ν.real Set.univ := by
    exact measureReal_mono (Set.subset_univ _) (by finiteness)
  have hboundedIntegrable : IntegrableOn tail (Ioc 0 R) volume := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      htailMeasurable.aestronglyMeasurable (ν.real Set.univ)
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    exact htailLeTotal t
  have htailZero : IntegrableOn tail (Ioi 0) volume := by
    have hset : Ioi R ∪ Ioc 0 R = Ioi 0 := by
      ext t
      simp only [mem_union, mem_Ioi, mem_Ioc]
      constructor
      · intro ht
        rcases ht with ht | ⟨ht, _⟩
        · exact lt_trans hRpos ht
        · exact ht
      · intro ht
        by_cases hRt : R < t
        · exact Or.inl hRt
        · exact Or.inr ⟨ht, le_of_not_gt hRt⟩
    rw [← hset]
    exact htailIntegrable.union hboundedIntegrable
  exact integrable_id_of_integrableOn_twoSidedTail ν htailZero


end ProbabilityTheory

end
