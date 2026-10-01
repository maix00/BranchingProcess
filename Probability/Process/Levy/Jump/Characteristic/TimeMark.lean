import Probability.Process.Levy.Jump.Intensity.Cutoff
import Probability.Process.Levy.Exponent.FiniteVariation
import Probability.Process.Levy.Jump.Characteristic.Independent

/-!
# Characteristic intensity across time and jump cutoffs

The two independent Poisson sources used for a jump-sum path have the
small- and large-jump restrictions of the same Lévy mark measure. The
unit-time product intensities therefore recover the original exponent.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- Integrating an uncompensated jump exponent over the two disjoint
unit-time sources gives exactly the unsplit Lévy exponent. -/
theorem IsLevyMeasure.integral_unitTime_uncompensated_split
    {ν : Measure ℝ} [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν)
    (n : ℕ) (ξ : ℝ) :
    (∫ z : unitInterval × ℝ, levyUncompensatedIntegrand ξ z.2
      ∂((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n)))) +
    (∫ z : unitInterval × ℝ, levyUncompensatedIntegrand ξ z.2
      ∂((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n)))) =
    ∫ x, levyUncompensatedIntegrand ξ x ∂ν := by
  have hf := hν.integrable_uncompensatedIntegrand hsmall ξ
  have hs : Integrable (levyUncompensatedIntegrand ξ)
      (ν.restrict (smallJumpBand n)) :=
    hf.mono_measure Measure.restrict_le_self
  have hl : Integrable (levyUncompensatedIntegrand ξ)
      (ν.restrict (largeJumpBand n)) :=
    hf.mono_measure Measure.restrict_le_self
  rw [integral_unitTime_prod_mark _ _ hs,
    integral_unitTime_prod_mark _ _ hl]
  exact hν.integral_smallJumpBand_add_largeJumpBand n hf

/-- The endpoint sum of independent small- and large-jump Poisson sources
has the characteristic exponent of the unsplit Lévy measure. The large-jump
first moment is not required. -/
theorem integral_exp_unitTime_split_poissonRandomMeasures
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hν : IsLevyMeasure ν) (hsmall : Integrable smallJumpDisplacement ν)
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) Pb)
    (hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))))
    (hbigfinite : ν (largeJumpBand n) < ⊤)
    (ξ : ℝ) :
    (∫ ω : Ωs × Ωb,
      Complex.exp (((ξ * ((∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
          (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
        Complex.I) ∂(Ps.prod Pb)) =
      Complex.exp (∫ x, levyUncompensatedIntegrand ξ x ∂ν) := by
  let gs : unitInterval × ℝ → ℂ := fun z =>
    Complex.exp (((ξ * z.2 : ℝ) : ℂ) * Complex.I) - 1
  have hbase : Integrable (levyUncompensatedIntegrand ξ) ν :=
    hν.integrable_uncompensatedIntegrand hsmall ξ
  have hgeq (x : ℝ) :
      Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I) - 1 =
        levyUncompensatedIntegrand ξ x := by
    simp only [levyUncompensatedIntegrand]
    congr 1
    push_cast
    ring
  have hgmark : Integrable
      (fun x : ℝ => Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I) - 1) ν := by
    simpa only [hgeq] using hbase
  have hgs : Integrable gs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) := by
    exact (hgmark.mono_measure Measure.restrict_le_self).comp_snd _
  have hgb : Integrable gs
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) := by
    exact (hgmark.mono_measure Measure.restrict_le_self).comp_snd _
  have hsreal := hds.ae_integrable_poissonRandomMeasure
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
    (by
      have hn : (∫⁻ z, ‖z.2‖ₑ
          ∂((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n)))) < ⊤ :=
        hasFiniteIntegral_iff_enorm.mp hsfirst.hasFiniteIntegral
      simpa only [Real.enorm_eq_ofReal_abs] using hn)
  have hbmass : ((volume : Measure unitInterval).prod
      (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact hbigfinite
  have hbreal := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbmass
  rw [integral_exp_sum_independent_poissonRandomMeasures hds hdb
    (by fun_prop) (by fun_prop) ξ hsreal hbreal hgs hgb]
  congr 1
  simpa only [gs, hgeq] using
    hν.integral_unitTime_uncompensated_split hsmall n ξ

/-- The endpoint law of the full small-plus-large jump sum is determined by
the given uncompensated characteristic exponent. This identification does
not use a favorable jump window or an entrance event. -/
theorem law_unitTime_split_poissonRandomMeasures
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν μ : Measure ℝ} [SigmaFinite ν] [IsProbabilityMeasure μ]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hν : IsLevyMeasure ν) (hsmall : Integrable smallJumpDisplacement ν)
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) Pb)
    (hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))))
    (hbigfinite : ν (largeJumpBand n) < ⊤)
    (hμ : ∀ ξ : ℝ, charFun μ ξ =
      Complex.exp (∫ x, levyUncompensatedIntegrand ξ x ∂ν)) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2))) = μ := by
  let F : Ωs × Ωb → ℝ := fun ω =>
    (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
    (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2))
  have hbigmass : ((volume : Measure unitInterval).prod
      (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rwa [hmass]
  have hsreal := hds.ae_integrable_poissonRandomMeasure
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
    (by
      have hn : (∫⁻ z, ‖z.2‖ₑ
          ∂((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n)))) < ⊤ :=
        hasFiniteIntegral_iff_enorm.mp hsfirst.hasFiniteIntegral
      simpa only [Real.enorm_eq_ofReal_abs] using hn)
  have hbreal := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbigmass
  have hF : AEMeasurable F (Ps.prod Pb) :=
    (hds.aemeasurable_integral_poissonRandomMeasure (by fun_prop) hsreal).comp_fst.add
      (hdb.aemeasurable_integral_poissonRandomMeasure (by fun_prop) hbreal).comp_snd
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_apply_real, integral_map hF (by fun_prop)]
  simpa only [F, Complex.ofReal_mul, mul_assoc] using
    (integral_exp_unitTime_split_poissonRandomMeasures hν hsmall n hds hdb
      hsfirst hbigfinite ξ).trans (hμ ξ).symm

end ProbabilityTheory
