import Probability.Process.Levy.Jump.Characteristic.PoissonIntegral
import Probability.Process.Levy.Jump.Intensity.TimeMark
import Probability.Process.Levy.Exponent.FiniteVariation

/-!
# Characteristic function of a jump sum in a time window

The time-window exponent is the window's Lebesgue mass times the mark
exponent. This result uses a general measurable window and does not
assume that the mark distribution has a global first moment.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem IsPoissonPointFamily.integral_exp_timeWindow_jumpSum
    {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X
      ((volume : Measure unitInterval).prod ν) P)
    (S : Set unitInterval) (hS : MeasurableSet S) (ξ : ℝ)
    (hrealized : ∀ᵐ ω ∂P,
      Integrable (fun z : unitInterval × ℝ => if z.1 ∈ S then z.2 else 0)
        (poissonRandomMeasure K X ω))
    (hmark : Integrable (levyUncompensatedIntegrand ξ) ν) :
    (∫ ω, Complex.exp (((ξ * (∫ z,
        (if z.1 ∈ S then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure K X ω)) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp (((volume : Measure unitInterval) S).toReal •
        (∫ x, levyUncompensatedIntegrand ξ x ∂ν)) := by
  let f : unitInterval × ℝ → ℝ := fun z => if z.1 ∈ S then z.2 else 0
  let g : ℝ → ℂ := levyUncompensatedIntegrand ξ
  have hf : Measurable f := by
    exact Measurable.ite (hS.preimage measurable_fst) measurable_snd measurable_const
  have hg : Integrable (fun z : unitInterval × ℝ => g z.2)
      ((volume : Measure unitInterval).prod ν) := hmark.comp_snd _
  have hprod : MeasurableSet (S ×ˢ Set.univ : Set (unitInterval × ℝ)) :=
    hS.prod MeasurableSet.univ
  have hpoint (z : unitInterval × ℝ) :
      Complex.exp (((ξ * f z : ℝ) : ℂ) * Complex.I) - 1 =
        (S ×ˢ Set.univ).indicator (fun z => g z.2) z := by
    by_cases hz : z.1 ∈ S
    · simp [f, g, hz, levyUncompensatedIntegrand]
      congr 1
      push_cast
      ring
    · simp [f, hz]
  have hintensity : Integrable
      (fun z : unitInterval × ℝ =>
        Complex.exp (((ξ * f z : ℝ) : ℂ) * Complex.I) - 1)
      ((volume : Measure unitInterval).prod ν) := by
    simp_rw [hpoint]
    exact hg.indicator hprod
  have hchar := hd.integral_exp_poissonRandomMeasure hf ξ hrealized hintensity
  change (∫ ω, Complex.exp (((ξ * (∫ z, f z ∂(poissonRandomMeasure K X ω)) : ℝ) : ℂ) *
    Complex.I) ∂P) = _
  rw [hchar]
  congr 1
  simp_rw [hpoint]
  rw [integral_indicator hprod]
  exact integral_timeWindow_prod_mark ν S hS g hmark

/-- Independent jump sources add their exponents on the same measurable
time window. -/
theorem integral_exp_sum_timeWindow_jumpSums
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {νs νb : Measure ℝ} [SigmaFinite νs] [SigmaFinite νb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod νs) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod νb) Pb)
    (S : Set unitInterval) (hS : MeasurableSet S) (ξ : ℝ)
    (hsreal : ∀ᵐ ω ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω))
    (hbreal : ∀ᵐ ω ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω))
    (hsmark : Integrable (levyUncompensatedIntegrand ξ) νs)
    (hbmark : Integrable (levyUncompensatedIntegrand ξ) νb) :
    (∫ ω : Ωs × Ωb,
      Complex.exp (((ξ * ((∫ z,
          (if z.1 ∈ S then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) * Complex.I)
      ∂(Ps.prod Pb)) =
    Complex.exp (((volume : Measure unitInterval) S).toReal •
      ((∫ x, levyUncompensatedIntegrand ξ x ∂νs) +
       (∫ x, levyUncompensatedIntegrand ξ x ∂νb))) := by
  let Us : Ωs → ℝ := fun ω =>
    ∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ) ∂(poissonRandomMeasure Ks Xs ω)
  let Ub : Ωb → ℝ := fun ω =>
    ∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ) ∂(poissonRandomMeasure Kb Xb ω)
  have hpoint (ω : Ωs × Ωb) :
      Complex.exp (((ξ * (Us ω.1 + Ub ω.2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((ξ * Us ω.1 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((ξ * Ub ω.2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  change (∫ ω, Complex.exp (((ξ * (Us ω.1 + Ub ω.2) : ℝ) : ℂ) * Complex.I)
    ∂(Ps.prod Pb)) = _
  simp_rw [hpoint]
  let u : Ωs → ℂ := fun ω => Complex.exp (((ξ * Us ω : ℝ) : ℂ) * Complex.I)
  let v : Ωb → ℂ := fun ω => Complex.exp (((ξ * Ub ω : ℝ) : ℂ) * Complex.I)
  change (∫ ω, u ω.1 * v ω.2 ∂(Ps.prod Pb)) = _
  rw [integral_prod_mul]
  change (∫ ω, Complex.exp (((ξ * Us ω : ℝ) : ℂ) * Complex.I) ∂Ps) *
    (∫ ω, Complex.exp (((ξ * Ub ω : ℝ) : ℂ) * Complex.I) ∂Pb) = _
  rw [hds.integral_exp_timeWindow_jumpSum S hS ξ hsreal hsmark,
    hdb.integral_exp_timeWindow_jumpSum S hS ξ hbreal hbmark,
    ← Complex.exp_add, smul_add]

end ProbabilityTheory
