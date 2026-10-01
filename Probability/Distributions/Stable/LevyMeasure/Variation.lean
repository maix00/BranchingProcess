import Probability.Distributions.Stable.LevyMeasure.Tails
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Small-jump variation of stable Lévy measures

The tail identities give the `α < 1` integrability threshold by the
layer-cake formula.
-/

namespace ProbabilityTheory

open MeasureTheory Set ENNReal

private theorem integrable_rpow_neg_on_unit {α : ℝ} (hα : α < 1) :
    IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioo 0 1) := by
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)

private theorem lintegral_rpow_neg_on_unit_lt_top {α : ℝ} (hα : α < 1) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (-α)) ∂volume) < ⊤ := by
  exact (integrable_rpow_neg_on_unit hα).lintegral_lt_top

private theorem smallJumpMoment_eq_tailIntegral (ν : Measure ℝ) :
    (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ), ν {x : ℝ | t < min 1 |x|} := by
  apply lintegral_eq_lintegral_meas_lt
  · filter_upwards [] with x
    exact le_min (by norm_num) (abs_nonneg x)
  · exact (by fun_prop : Measurable (fun x : ℝ => min 1 |x|)).aemeasurable

/-- A power-law tail with index below one gives a finite truncated first moment. -/
theorem finite_smallJumpMoment_of_tailBound (ν : Measure ℝ)
    {α : ℝ} (hα : α < 1) (C : ENNReal) (hC : C < ⊤)
    (htail : ∀ t : ℝ, 0 < t →
      ν {x : ℝ | t < |x|} ≤ ENNReal.ofReal (t ^ (-α)) * C) :
    (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) < ⊤ := by
  rw [smallJumpMoment_eq_tailIntegral]
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      ν {x : ℝ | t < min 1 |x|} ≤
        (Iio (1 : ℝ)).indicator
          (fun t => ENNReal.ofReal (t ^ (-α)) * C) t := by
    intro t ht
    by_cases ht1 : t < 1
    · rw [Set.indicator_of_mem (show t ∈ Iio (1 : ℝ) from ht1)]
      have hset : {x : ℝ | t < min 1 |x|} = {x : ℝ | t < |x|} := by
        ext x
        simp only [Set.mem_ofPred_eq, lt_min_iff]
        exact and_iff_right ht1
      rw [hset]
      exact htail t ht
    · rw [Set.indicator_of_notMem (show t ∉ Iio (1 : ℝ) from ht1)]
      simp [lt_min_iff, ht1]
  calc
    (∫⁻ t in Ioi (0 : ℝ), ν {x : ℝ | t < min 1 |x|}) ≤
        ∫⁻ t in Ioi (0 : ℝ),
          (Iio (1 : ℝ)).indicator
            (fun t => ENNReal.ofReal (t ^ (-α)) * C) t := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact hbound t ht
    _ = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (-α)) * C := by
      rw [lintegral_indicator measurableSet_Iio]
      rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    _ < ⊤ := by
      rw [lintegral_mul_const' _ _ hC.ne]
      exact ENNReal.mul_lt_top (lintegral_rpow_neg_on_unit_lt_top hα) hC

/-- The stable Lévy measure has finite truncated first absolute moment for
`α < 1`. This is the measure-level finite-variation input for its jump sum. -/
theorem IsStrictlyAlphaStable.levyMeasure_smallJumpMoment_lt_top
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) :
    (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂T.levyMeasure) < ⊤ := by
  let C : ENNReal := T.levyMeasure (Iio (-1)) + T.levyMeasure (Ioi 1)
  have hfar := T.levyMeasure_isLevyMeasure.measure_setOf_abs_ge_lt_top one_pos
  have hminus : T.levyMeasure (Iio (-1)) < ⊤ := by
    apply (measure_mono _).trans_lt hfar
    intro x hx
    simp only [Set.mem_Iio, Set.mem_ofPred_eq] at hx ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hplus : T.levyMeasure (Ioi 1) < ⊤ := by
    apply (measure_mono _).trans_lt hfar
    intro x hx
    simp only [Set.mem_Ioi, Set.mem_ofPred_eq] at hx ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hC : C < ⊤ := ENNReal.add_lt_top.mpr ⟨hminus, hplus⟩
  apply finite_smallJumpMoment_of_tailBound T.levyMeasure hα C hC
  intro t ht
  rw [h.levyMeasure_abs_tail T hT ht]
  change ENNReal.ofReal ((1 / t) ^ α) * C ≤ ENNReal.ofReal (t ^ (-α)) * C
  have hpow : (1 / t) ^ α = t ^ (-α) := by
    rw [one_div, Real.inv_rpow ht.le, Real.rpow_neg ht.le]
  rw [hpow]

/-- Finite variation of jumps of size at most one, in the conventional
Lévy–Itô truncation. -/
theorem IsStrictlyAlphaStable.levyMeasure_integral_small_abs_lt_top
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) :
    (∫⁻ x in {x : ℝ | |x| ≤ 1}, ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤ := by
  calc
    (∫⁻ x in {x : ℝ | |x| ≤ 1}, ENNReal.ofReal |x| ∂T.levyMeasure) =
        ∫⁻ x in {x : ℝ | |x| ≤ 1},
          ENNReal.ofReal (min 1 |x|) ∂T.levyMeasure := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem
              (measurableSet_le (by fun_prop : Measurable (fun x : ℝ => |x|)) measurable_const)]
              with x hx
            rw [min_eq_right hx]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂T.levyMeasure :=
      setLIntegral_le_lintegral _ _
    _ < ⊤ := h.levyMeasure_smallJumpMoment_lt_top T hT hα

/-- The real-valued small-jump displacement is Bochner integrable, so its
uncompensated drift is a well-defined real number. -/
theorem IsStrictlyAlphaStable.levyMeasure_integrableOn_small
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) :
    IntegrableOn (fun x : ℝ => x) {x : ℝ | |x| ≤ 1} T.levyMeasure := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [Real.enorm_eq_ofReal_abs] using
    h.levyMeasure_integral_small_abs_lt_top T hT hα

end ProbabilityTheory
