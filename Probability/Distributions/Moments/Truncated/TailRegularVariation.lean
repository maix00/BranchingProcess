/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Integral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Layercake
public import Probability.Distributions.Moments.Truncated.TailIntegral

/-!
# First moments from regularly varying tails

For a probability law on `ℝ`, a regularly varying two-sided tail with index
less than `-1` gives a finite first absolute moment. The tail integral is
controlled by the existing Karamata theorem, whose proof uses the regular
variation Potter bound; Mathlib's layer-cake theorem then identifies it with
the first absolute moment.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory

/-- A probability measure with a regularly varying two-sided tail of index
`-α`, for `α > 1`, has an integrable identity function. -/
theorem integrable_id_of_twoSidedTail_regularlyVarying
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {α : ℝ}
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
  have htailLeOne (t : ℝ) : tail t ≤ 1 := by
    calc
      tail t ≤ ν.real Set.univ :=
        measureReal_mono (Set.subset_univ _) (by finiteness)
      _ = 1 := by simp
  have hboundedIntegrable : IntegrableOn tail (Ioc 0 R) volume := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      htailMeasurable.aestronglyMeasurable 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    exact htailLeOne t
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
  have htailRealIntegrable :
      Integrable tail (volume.restrict (Ioi (0 : ℝ))) := htailZero
  have htailRealLIntegralNeTop :
      (∫⁻ t, ENNReal.ofReal (tail t)
        ∂(volume.restrict (Ioi (0 : ℝ)))) ≠ ∞ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      htailRealIntegrable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => hnonneg t)).2 htailRealIntegrable
  have htailRealLIntegralFinite :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tail t) ∂volume) < ∞ := by
    exact lt_top_iff_ne_top.mpr (by simpa using htailRealLIntegralNeTop)
  let tailENN : ℝ → ℝ≥0∞ := fun t => ν {x : ℝ | t < |x|}
  have htailENN_eq (t : ℝ) : tailENN t = ENNReal.ofReal (tail t) := by
    dsimp [tailENN, tail]
    rw [Measure.real]
    exact (ENNReal.ofReal_toReal (measure_lt_top ν _).ne).symm
  have htailENNFinite :
      (∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume) < ∞ := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume) =
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tail t) ∂volume := by
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall htailENN_eq
      _ < ∞ := htailRealLIntegralFinite
  have hlayercake :
      (∫⁻ x, ENNReal.ofReal |x| ∂ν) =
        ∫⁻ t in Ioi (0 : ℝ), tailENN t ∂volume := by
    exact lintegral_eq_lintegral_meas_lt ν
      (Filter.Eventually.of_forall fun x => abs_nonneg x)
      continuous_abs.measurable.aemeasurable
  have habsoluteLIntegralNeTop :
      (∫⁻ x, ENNReal.ofReal |x| ∂ν) ≠ ∞ := by
    rw [hlayercake]
    exact htailENNFinite.ne
  have habsolute : Integrable (fun x : ℝ => |x|) ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      continuous_abs.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => abs_nonneg x)).1
      habsoluteLIntegralNeTop
  have habsoluteNorm : Integrable (fun x : ℝ => ‖x‖) ν := by
    simpa [Real.norm_eq_abs] using habsolute
  exact (integrable_norm_iff (f := id) measurable_id.aestronglyMeasurable).1
    habsoluteNorm

end ProbabilityTheory

end
