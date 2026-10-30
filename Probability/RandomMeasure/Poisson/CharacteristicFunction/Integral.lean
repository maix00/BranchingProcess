/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Integration.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Probability.RandomMeasure.Poisson.Integration.Integrability
import Probability.RandomMeasure.Poisson.CharacteristicFunction.PartitionedSum

/-!
# Characteristic formula for a Poisson random-measure integral

## Public declarations

- `ProbabilityTheory.IsPoissonPointFamily.integral_exp_poissonRandomMeasure`: if the realized
  integral of `f` is almost surely integrable and `exp (i ξ f) - 1` is
  integrable against the intensity `m`, then
  `∫ exp (i ξ ∫ f dN) dP = exp (∫ (exp (i ξ f) - 1) dm)`.
- `ProbabilityTheory.IsPoissonPointFamily.charFun_poissonRandomMeasure_integral`: the same
  identity for the characteristic function of the law of `∫ f dN`.
- `ProbabilityTheory.IsPoissonPointFamily.integral_exp_poissonRandomMeasure_of_integrable`:
  the exponential-integral formula when `f` is integrable against `m`.
- `ProbabilityTheory.IsPoissonPointFamily.integral_exp_poissonRandomMeasure_of_finiteIntensity`:
  the formula when `m` has finite total mass, without a first-moment
  assumption on `f`.

The intensity integrand `exp (i ξ f) - 1` and almost-sure integrability of
the realized integral are stated as separate hypotheses in the general form.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Complex Filter
open scoped Topology

private lemma hasSum_integral_prmPiece
    {E : Type} [MeasurableSpace E]
    {m : Measure E} [SigmaFinite m]
    {g : E → ℂ} (hg : Integrable g m) :
    HasSum (fun k => ∫ x in prmPiece m k, g x ∂m)
      (∫ x, g x ∂m) := by
  have h := hasSum_integral_iUnion
    (s := prmPiece m) (f := g) (μ := m)
    (fun k => measurableSet_prmPiece)
    pairwise_disjoint_prmPiece (by simpa [iUnion_prmPiece] using hg)
  simpa only [iUnion_prmPiece, setIntegral_univ] using h

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
  let : IsFiniteMeasure m := ⟨hm⟩
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
