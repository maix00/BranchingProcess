/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Truncated moments from power-law tails

The layer-cake formula converts a power-law bound on the two-sided tail of
an arbitrary real measure into finiteness of its capped first absolute moment.

## Public declarations

- If $\nu(|x|>t)\le C t^{-\alpha}$ for every $t>0$, with $C<\infty$ and
  $\alpha<1$, then $\int \min(R,|x|)\,d\nu(x)<\infty$ for every $R>0$.
-/

@[expose] public section

namespace MeasureTheory

open Set ENNReal

private lemma integrable_rpow_neg_on {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioo 0 R) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  linarith

private lemma lintegral_rpow_neg_on_lt_top {α R : ℝ}
    (hα : α < 1) (hR : 0 < R) :
    (∫⁻ t in Ioo (0 : ℝ) R, ENNReal.ofReal (t ^ (-α)) ∂volume) < ⊤ := by
  exact (integrable_rpow_neg_on hα hR).lintegral_lt_top

private lemma lintegral_min_radius_abs_eq_tailIntegral (ν : Measure ℝ) {R : ℝ}
    (hR : 0 ≤ R) :
    (∫⁻ x, ENNReal.ofReal (min R |x|) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ), ν {x : ℝ | t < min R |x|} := by
  apply lintegral_eq_lintegral_meas_lt
  · filter_upwards [] with x
    exact le_min hR (abs_nonneg x)
  · exact (by fun_prop : Measurable (fun x : ℝ => min R |x|)).aemeasurable

/-- A power-law bound on the two-sided tail with exponent below one makes
every capped first absolute moment finite. No probability or stability
assumption is needed on the measure. -/
theorem lintegral_min_radius_abs_lt_top_of_power_tail_bound (ν : Measure ℝ)
    {α R : ℝ} (hα : α < 1) (hR : 0 < R) (C : ℝ≥0∞) (hC : C < ⊤)
    (htail : ∀ t : ℝ, 0 < t →
      ν {x : ℝ | t < |x|} ≤ ENNReal.ofReal (t ^ (-α)) * C) :
    (∫⁻ x, ENNReal.ofReal (min R |x|) ∂ν) < ⊤ := by
  rw [lintegral_min_radius_abs_eq_tailIntegral ν hR.le]
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      ν {x : ℝ | t < min R |x|} ≤
        (Iio R).indicator
          (fun t => ENNReal.ofReal (t ^ (-α)) * C) t := by
    intro t ht
    by_cases htR : t < R
    · rw [Set.indicator_of_mem (show t ∈ Iio R from htR)]
      have hset : {x : ℝ | t < min R |x|} = {x : ℝ | t < |x|} := by
        ext x
        simp only [Set.mem_ofPred_eq, lt_min_iff]
        exact and_iff_right htR
      rw [hset]
      exact htail t ht
    · rw [Set.indicator_of_notMem (show t ∉ Iio R from htR)]
      simp [lt_min_iff, htR]
  calc
    (∫⁻ t in Ioi (0 : ℝ), ν {x : ℝ | t < min R |x|}) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (Iio R).indicator
            (fun t => ENNReal.ofReal (t ^ (-α)) * C) t := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact hbound t ht
    _ = ∫⁻ t in Ioo (0 : ℝ) R, ENNReal.ofReal (t ^ (-α)) * C := by
      rw [lintegral_indicator measurableSet_Iio]
      rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    _ < ⊤ := by
      rw [lintegral_mul_const' _ _ hC.ne]
      exact ENNReal.mul_lt_top (lintegral_rpow_neg_on_lt_top hα hR) hC

end MeasureTheory
