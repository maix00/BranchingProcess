import Probability.Distributions.Stable.LevyMeasure.Drift
import Probability.Distributions.Stable.LevyMeasure.Cutoff
import Probability.Process.Levy.Jump.Characteristic.TimeMark
import Probability.Process.Levy.Jump.PoissonConfiguration.Endpoint

/-!
# Endpoint law of the stable jump-sum model

For an index below one, every fixed small/large jump cutoff yields the
given strictly stable law at unit time. The proof uses the uncompensated
characteristic exponent and imposes no moment on the large jumps.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem IsStrictlyAlphaStable.law_unitTime_split_poissonRandomMeasures
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2))) = μ := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
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
  exact ProbabilityTheory.law_unitTime_split_poissonRandomMeasures
    T.levyMeasure_isLevyMeasure hsmall n hds hdb hsfirst
    (T.levyMeasure_largeJumpBand_lt_top n)
    (h.charFun_eq_exp_integral_uncompensated T hT hα)

/-- The endpoint of the actual cutoff path in the one-jump entrance
construction has the prescribed stable law. -/
theorem IsStrictlyAlphaStable.law_poissonEntrancePath_cutoff_top
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    (Ps.prod Pb).map (poissonEntrancePath Ks Xs Kb Xb
      (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) ⊤) = μ := by
  rw [Measure.map_congr (ae_poissonEntrancePath_cutoff_top_eq_integral n hds hdb)]
  exact h.law_unitTime_split_poissonRandomMeasures T hT hα n hds hdb

end ProbabilityTheory
