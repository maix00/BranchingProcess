/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Jump.Characteristic.PoissonIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent Poisson jump sources

The characteristic exponent of a sum of two independent Poisson jump
integrals is the sum of their intensity exponents. Product integration
supplies the independence directly; no extra random-measure structure is
introduced.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Complex

theorem integral_exp_sum_independent_poissonRandomMeasures
    {Ωs Ωb E : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    [MeasurableSpace E]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → E}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → E}
    {ms mb : Measure E} [SigmaFinite ms] [SigmaFinite mb] [Nonempty E]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    {fs fb : E → ℝ} (hfs : Measurable fs) (hfb : Measurable fb)
    (ξ : ℝ)
    (hsreal : ∀ᵐ ω ∂Ps, Integrable fs (poissonRandomMeasure Ks Xs ω))
    (hbreal : ∀ᵐ ω ∂Pb, Integrable fb (poissonRandomMeasure Kb Xb ω))
    (hsint : Integrable
      (fun x => Complex.exp (((ξ * fs x : ℝ) : ℂ) * Complex.I) - 1) ms)
    (hbint : Integrable
      (fun x => Complex.exp (((ξ * fb x : ℝ) : ℂ) * Complex.I) - 1) mb) :
    (∫ ω : Ωs × Ωb,
      Complex.exp (((ξ * ((∫ x, fs x ∂(poissonRandomMeasure Ks Xs ω.1)) +
          (∫ x, fb x ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
        Complex.I) ∂(Ps.prod Pb)) =
      Complex.exp
        ((∫ x, (Complex.exp (((ξ * fs x : ℝ) : ℂ) * Complex.I) - 1) ∂ms) +
         (∫ x, (Complex.exp (((ξ * fb x : ℝ) : ℂ) * Complex.I) - 1) ∂mb)) := by
  have hpoint (ω : Ωs × Ωb) :
      Complex.exp (((ξ * ((∫ x, fs x ∂(poissonRandomMeasure Ks Xs ω.1)) +
          (∫ x, fb x ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
        Complex.I) =
      Complex.exp (((ξ * ∫ x, fs x ∂(poissonRandomMeasure Ks Xs ω.1) : ℝ) : ℂ) *
        Complex.I) *
      Complex.exp (((ξ * ∫ x, fb x ∂(poissonRandomMeasure Kb Xb ω.2) : ℝ) : ℂ) *
        Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpoint]
  let u : Ωs → ℂ := fun ω =>
    Complex.exp (((ξ * ∫ x, fs x ∂(poissonRandomMeasure Ks Xs ω) : ℝ) : ℂ) * Complex.I)
  let v : Ωb → ℂ := fun ω =>
    Complex.exp (((ξ * ∫ x, fb x ∂(poissonRandomMeasure Kb Xb ω) : ℝ) : ℂ) * Complex.I)
  change (∫ ω, u ω.1 * v ω.2 ∂(Ps.prod Pb)) = _
  rw [integral_prod_mul]
  change (∫ ω, Complex.exp (((ξ * ∫ x, fs x ∂(poissonRandomMeasure Ks Xs ω) : ℝ) : ℂ) *
    Complex.I) ∂Ps) *
    (∫ ω, Complex.exp (((ξ * ∫ x, fb x ∂(poissonRandomMeasure Kb Xb ω) : ℝ) : ℂ) *
      Complex.I) ∂Pb) = _
  rw [
    hds.integral_exp_poissonRandomMeasure hfs ξ hsreal hsint,
    hdb.integral_exp_poissonRandomMeasure hfb ξ hbreal hbint,
    ← Complex.exp_add]

end ProbabilityTheory
