/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.Distributions.Stable.LevyMeasure.Drift
public import MeasureTheory.Measure.LevyMeasure.Cutoff
import Probability.RandomMeasure.Poisson.TimeMark

/-!
# Finite-variation cutoff for a stable Lévy measure

For index below one, the stable Lévy measure has a deterministic cutoff with
arbitrarily small absolute-jump intensity. Jumps outside that cutoff have
finite intensity.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem IsStrictlyAlphaStable.exists_smallJumpBand_lintegral_lt
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n : ℕ,
      (∫⁻ x in smallJumpBand n, ENNReal.ofReal |x|
        ∂T.levyMeasure) < ENNReal.ofReal ρ :=
  ProbabilityTheory.exists_smallJumpBand_lintegral_lt T.levyMeasure
    (h.levyMeasure_smallJumpMoment_lt_top T hT hα).ne ρ hρ

/-- Every reciprocal cutoff has finite large-jump intensity. -/
theorem LevyKhintchineTriple.levyMeasure_largeJumpBand_lt_top
    (T : LevyKhintchineTriple) (n : ℕ) :
    T.levyMeasure (largeJumpBand n) < ⊤ := by
  have hcut : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  exact T.isLevyMeasure.measure_setOf_abs_ge_lt_top hcut

/-- The unit-time small-jump source has an integrable mark projection.
No corresponding assertion is made for the large-jump source. -/
theorem IsStrictlyAlphaStable.integrable_unitTime_smallJumpMark
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (n : ℕ) :
    Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) := by
  refine ⟨(by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs]
  rw [lintegral_unitTime_prod_mark
    (T.levyMeasure.restrict (smallJumpBand n))
    (fun x => ENNReal.ofReal |x|) (by fun_prop)]
  exact (lintegral_smallJumpBand_abs_eq_min T.levyMeasure n).trans_lt
    ((setLIntegral_le_lintegral _ _).trans_lt
      (h.levyMeasure_smallJumpMoment_lt_top T hT hα))

/-- The same cutoff gives the exact unit-time intensities needed by the
independent small/large Poisson construction. -/
theorem IsStrictlyAlphaStable.exists_unitTime_jumpIntensity_cutoff
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ n : ℕ,
      1 / ((n : ℝ) + 1) < δ ∧
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) <
          ENNReal.ofReal ρ ∧
      ((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  let : SigmaFinite T.levyMeasure := T.isLevyMeasure.sigmaFinite
  obtain ⟨n, hn, hrad⟩ :=
    ProbabilityTheory.exists_smallJumpBand_lintegral_lt_and_radius_lt
      T.levyMeasure (h.levyMeasure_smallJumpMoment_lt_top T hT hα).ne
      ρ δ hρ hδ
  refine ⟨n, hrad, ?_, ?_⟩
  · rw [lintegral_unitTime_prod_mark
      (T.levyMeasure.restrict (smallJumpBand n))
      (fun x => ENNReal.ofReal |x|) (by fun_prop)]
    exact hn
  · have hmass := unitTime_prod_markWindow
      (T.levyMeasure.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact T.levyMeasure_largeJumpBand_lt_top n

end ProbabilityTheory
