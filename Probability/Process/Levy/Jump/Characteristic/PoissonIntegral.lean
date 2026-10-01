import Probability.Process.Levy.Jump.Characteristic.Integral
import Probability.Process.Levy.Jump.Campbell.Integrability
import Probability.Process.Levy.Jump.Campbell.FiniteActivity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Characteristic formula for an uncompensated Poisson integral

The intensity integrand `exp (i ξ f) - 1` must be integrable, while the
realized jump integral need only be integrable almost surely. These are
separate hypotheses so that the theorem also applies to finite-activity
large jumps without assuming their global first moment.
-/

namespace ProbabilityTheory

open MeasureTheory Complex Filter
open scoped Topology

theorem IsPoissonPointFamily.integral_exp_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (ξ : ℝ)
    (hrealized : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω))
    (hintensity : Integrable
      (fun x => Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) m) :
    (∫ ω, Complex.exp (((ξ * ∫ x, f x ∂(poissonRandomMeasure K X ω) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      Complex.exp (∫ x, (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
  let S : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω
  let F : ℕ → Ω → ℂ := fun n ω =>
    Complex.exp (((ξ * S n ω : ℝ) : ℂ) * Complex.I)
  let G : Ω → ℂ := fun ω =>
    Complex.exp (((ξ * ∫ x, f x ∂(poissonRandomMeasure K X ω) : ℝ) : ℂ) *
      Complex.I)
  have hSmeas (n : ℕ) : Measurable (S n) := by
    exact Finset.measurable_sum _ fun k _ =>
      measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) P := by
    have hm : Measurable (F n) := by fun_prop
    exact hm.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro ω
    simpa [F] using (Complex.norm_exp_ofReal_mul_I (ξ * S n ω)).le
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hrealized] with ω hω
    have hs := (hasSum_pieceSum_poissonRandomMeasure K X ω hf hω).tendsto_sum_nat
    have hs' : Tendsto (fun n => S n ω) atTop
        (𝓝 (∫ x, f x ∂(poissonRandomMeasure K X ω))) := by
      simpa only [S, Function.comp_def] using hs.comp (tendsto_add_atTop_nat 1)
    have hc : Continuous (fun x : ℝ =>
        Complex.exp (((ξ * x : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hs'
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := P) (F := F) (f := G) (fun _ => (1 : ℝ)) hFmeas
    (integrable_const 1) hbound hlim
  have hfinite (n : ℕ) :
      (∫ ω, F n ω ∂P) =
        Complex.exp (∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece m k,
            (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
    have hmap : (∫ ω, F n ω ∂P) = charFun (P.map (S n)) ξ := by
      rw [charFun_apply_real, integral_map (hSmeas n).aemeasurable (by fun_prop)]
      congr 1
      funext ω
      simp only [F]
      congr 1
      push_cast
      ring
    rw [hmap]
    exact hd.charFun_prefixPieceSum_eq_exp_setIntegrals hf n ξ
  have hsum := (hasSum_integral_prmPiece hintensity).tendsto_sum_nat
  have hsum' : Tendsto
      (fun n => ∑ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece m k,
          (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m)
      atTop
      (𝓝 (∫ x, (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m)) :=
    hsum.comp (tendsto_add_atTop_nat 1)
  have hright := Complex.continuous_exp.continuousAt.tendsto.comp hsum'
  have hleft : Tendsto
      (fun n => Complex.exp (∑ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece m k,
          (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m))
      atTop (𝓝 (∫ ω, G ω ∂P)) := by
    simpa only [hfinite] using hDCT
  exact tendsto_nhds_unique hleft hright

/-- Characteristic-function form of the full Poisson integral formula. -/
theorem IsPoissonPointFamily.charFun_poissonRandomMeasure_integral
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (ξ : ℝ)
    (hrealized : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω))
    (hintensity : Integrable
      (fun x => Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) m) :
    charFun (P.map (fun ω => ∫ x, f x ∂(poissonRandomMeasure K X ω))) ξ =
      Complex.exp (∫ x, (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
  rw [charFun_apply_real,
    integral_map (hd.aemeasurable_integral_poissonRandomMeasure hf hrealized)
      (by fun_prop)]
  convert hd.integral_exp_poissonRandomMeasure hf ξ hrealized hintensity using 1
  congr 1
  funext ω
  congr 1
  push_cast
  ring

/-- The formula under a global first moment. This is the form directly
applicable to the small-jump source of an index-below-one stable law. -/
theorem IsPoissonPointFamily.integral_exp_poissonRandomMeasure_of_integrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (hfirst : Integrable f m) (ξ : ℝ) :
    (∫ ω, Complex.exp (((ξ * ∫ x, f x ∂(poissonRandomMeasure K X ω) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      Complex.exp (∫ x, (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
  have hfinite : (∫⁻ x, ENNReal.ofReal |f x| ∂m) < ⊤ := by
    have hn : (∫⁻ x, ‖f x‖ₑ ∂m) < ⊤ :=
      hasFiniteIntegral_iff_enorm.mp hfirst.hasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal_abs] using hn
  have hrealized := hd.ae_integrable_poissonRandomMeasure hf hfinite
  have hintensity : Integrable
      (fun x => Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) m := by
    apply Integrable.mono' (hfirst.norm.const_mul |ξ|) (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    calc
      ‖Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1‖ =
          ‖Complex.exp (Complex.I * ((ξ * f x : ℝ) : ℂ)) - 1‖ := by
            rw [mul_comm (((ξ * f x : ℝ) : ℂ)) Complex.I]
      _ ≤ ‖ξ * f x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |ξ| * |f x| := by simp [Real.norm_eq_abs]
  exact hd.integral_exp_poissonRandomMeasure hf ξ hrealized hintensity

/-- The formula for a finite-activity source. Its jump sizes may have an
infinite first moment: the realized number of jumps is finite almost surely,
and the complex exponential difference is uniformly bounded. -/
theorem IsPoissonPointFamily.integral_exp_poissonRandomMeasure_of_finiteIntensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (hm : m Set.univ < ⊤) (ξ : ℝ) :
    (∫ ω, Complex.exp (((ξ * ∫ x, f x ∂(poissonRandomMeasure K X ω) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      Complex.exp (∫ x, (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
  letI : IsFiniteMeasure m := ⟨hm⟩
  have hrealized := hd.ae_integrable_of_finite_intensity hf hm
  have hintensity : Integrable
      (fun x => Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) m := by
    apply Integrable.mono' (integrable_const (2 : ℝ)) (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    calc
      ‖Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          ‖Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
  exact hd.integral_exp_poissonRandomMeasure hf ξ hrealized hintensity

end ProbabilityTheory
