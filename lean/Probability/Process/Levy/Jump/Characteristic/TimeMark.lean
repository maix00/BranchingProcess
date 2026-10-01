import Probability.Process.Levy.Jump.Intensity.Cutoff
import Probability.Process.Levy.Exponent.FiniteVariation
import Probability.Process.Levy.Jump.Characteristic.Independent
import Probability.Process.Levy.Jump.Characteristic.TimeWindow

/-!
# Characteristic intensity across time and jump cutoffs

The two independent Poisson sources used for a jump-sum path have the
small- and large-jump restrictions of the same Lévy mark measure. The
unit-time product intensities therefore recover the original exponent.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

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

set_option maxHeartbeats 800000 in
/-- For every measurable observation window, the two cutoff sources have
the unsplit Lévy exponent multiplied by the window's Lebesgue mass. -/
theorem integral_exp_timeWindow_split_poissonRandomMeasures
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
    (S : Set unitInterval) (hS : MeasurableSet S) (ξ : ℝ) :
    (∫ ω : Ωs × Ωb,
      Complex.exp (((ξ * ((∫ z,
          (if z.1 ∈ S then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) * Complex.I)
      ∂(Ps.prod Pb)) =
    Complex.exp (((volume : Measure unitInterval) S).toReal •
      (∫ x, levyUncompensatedIntegrand ξ x ∂ν)) := by
  have hsmallreal := hds.ae_integrable_poissonRandomMeasure
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
    (by
      have hn : (∫⁻ z, ‖z.2‖ₑ
          ∂((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n)))) < ⊤ :=
        hasFiniteIntegral_iff_enorm.mp hsfirst.hasFiniteIntegral
      simpa only [Real.enorm_eq_ofReal_abs] using hn)
  have hbigmass : ((volume : Measure unitInterval).prod
      (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rwa [hmass]
  have hbigreal := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbigmass
  have hregion : MeasurableSet (S ×ˢ Set.univ : Set (unitInterval × ℝ)) :=
    hS.prod MeasurableSet.univ
  have hsreal : ∀ᵐ ω ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω) := by
    filter_upwards [hsmallreal] with ω hω
    exact hω.indicator (hS.preimage measurable_fst)
  have hbreal : ∀ᵐ ω ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω) := by
    filter_upwards [hbigreal] with ω hω
    exact hω.indicator (hS.preimage measurable_fst)
  have hg := hν.integrable_uncompensatedIntegrand hsmall ξ
  have hgs := hg.mono_measure (Measure.restrict_le_self (s := smallJumpBand n))
  have hgb := hg.mono_measure (Measure.restrict_le_self (s := largeJumpBand n))
  have hchar := integral_exp_sum_timeWindow_jumpSums hds hdb S hS ξ
    hsreal hbreal hgs hgb
  rw [hchar]
  congr 1
  rw [hν.integral_smallJumpBand_add_largeJumpBand n hg]

set_option maxHeartbeats 800000 in
/-- The sum of jump contributions from a measurable time window has the
law prescribed by the unsplit Lévy exponent at that window length. -/
theorem law_timeWindow_split_poissonRandomMeasures
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
    (S : Set unitInterval) (hS : MeasurableSet S)
    (hμ : ∀ ξ : ℝ, charFun μ ξ =
      Complex.exp (((volume : Measure unitInterval) S).toReal •
        (∫ x, levyUncompensatedIntegrand ξ x ∂ν))) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2))) = μ := by
  let f : unitInterval × ℝ → ℝ := fun z => if z.1 ∈ S then z.2 else 0
  let F : Ωs × Ωb → ℝ := fun ω =>
    (∫ z, f z ∂(poissonRandomMeasure Ks Xs ω.1)) +
    (∫ z, f z ∂(poissonRandomMeasure Kb Xb ω.2))
  have hf : Measurable f :=
    Measurable.ite (hS.preimage measurable_fst) measurable_snd measurable_const
  have hsreal0 := hds.ae_integrable_poissonRandomMeasure
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
    rwa [hmass]
  have hbreal0 := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbmass
  have hsreal : ∀ᵐ ω ∂Ps, Integrable f (poissonRandomMeasure Ks Xs ω) := by
    filter_upwards [hsreal0] with ω hω
    exact hω.indicator (hS.preimage measurable_fst)
  have hbreal : ∀ᵐ ω ∂Pb, Integrable f (poissonRandomMeasure Kb Xb ω) := by
    filter_upwards [hbreal0] with ω hω
    exact hω.indicator (hS.preimage measurable_fst)
  have hF : AEMeasurable F (Ps.prod Pb) :=
    (hds.aemeasurable_integral_poissonRandomMeasure hf hsreal).comp_fst.add
      (hdb.aemeasurable_integral_poissonRandomMeasure hf hbreal).comp_snd
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_apply_real, integral_map hF (by fun_prop)]
  simpa only [F, f, Complex.ofReal_mul, mul_assoc] using
    (integral_exp_timeWindow_split_poissonRandomMeasures hν hsmall n hds hdb
      hsfirst hbigfinite S hS ξ).trans (hμ ξ).symm

end ProbabilityTheory
