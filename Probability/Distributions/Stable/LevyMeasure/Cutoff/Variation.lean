/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Probability.Distributions.Stable.LevyMeasure.Tail.Homogeneous
import MeasureTheory.Measure.Tails.Power

/-!
# Small-jump variation of stable Lévy measures

The tail identities give the `α < 1` integrability threshold by the
layer-cake formula.

If `ν` is the Lévy measure of a strictly `α`-stable law and `α<1`, the
truncated first moment and the first absolute moment of the small jumps are
finite:

\[
\begin{aligned}
\int_{\mathbb R}\min(1,|x|)\,\nu(dx)&<\infty,\\
\int_{|x|\leq1}|x|\,\nu(dx)&<\infty.
\end{aligned}
\]

## Public declarations

* `levyMeasure_smallJumpMoment_lt_top` states
  `∫⁻ min(1, |x|) dν < ∞` for `α < 1`.
* `levyMeasure_integral_small_abs_lt_top` gives finite first absolute moment
  on `|x| ≤ 1`, and `levyMeasure_integrableOn_small` gives integrability of
  `x` on that set.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set ENNReal

/-- The stable Lévy measure has finite truncated first absolute moment for
`α < 1`. This is the measure-level finite-variation input for its jump sum. -/
theorem IsStrictlyAlphaStable.levyMeasure_smallJumpMoment_lt_top
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) :
    (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂T.levyMeasure) < ⊤ := by
  let C : ENNReal := T.levyMeasure (Iio (-1)) + T.levyMeasure (Ioi 1)
  have hfar := T.isLevyMeasure.measure_setOf_abs_ge_lt_top one_pos
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
  apply MeasureTheory.lintegral_min_radius_abs_lt_top_of_power_tail_bound
    T.levyMeasure hα one_pos C hC
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
