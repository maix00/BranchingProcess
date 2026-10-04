/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Compact-uniform convergence of characteristic functions

Weak convergence of probability measures implies uniform convergence of their
characteristic functions on compact frequency sets.  The proof uses tightness
to obtain equicontinuity and then the compactness criterion for uniform
convergence in Mathlib.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace MeasureTheory

/-- A tight family of probability measures has an equicontinuous family of
characteristic functions. -/
theorem equicontinuous_charFun_of_isTightMeasureSet
    {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : IsTightMeasureSet (Set.range μ)) :
    Equicontinuous (fun n t => charFun (μ n) t) := by
  intro t U hU
  obtain ⟨ε, hε, hUε⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨K, hK, hTail⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ)
      (ENNReal.ofReal (ε / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  let δ : ℝ := ε / (4 * (R + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hEqui : ∀ n s t, dist s t < δ → dist (charFun (μ n) s) (charFun (μ n) t) < ε := by
    intro n s t hst
    let f : ℝ → ℂ := fun x => Complex.exp (s * x * Complex.I)
    let g : ℝ → ℂ := fun x => Complex.exp (t * x * Complex.I)
    have hf : Integrable f (μ n) := by
      refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
      simp [f, Complex.norm_exp]
    have hg : Integrable g (μ n) := by
      refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
      simp [g, Complex.norm_exp]
    have hdiffInt : Integrable (fun x => ‖f x - g x‖) (μ n) := by
      refine Integrable.mono' (integrable_const (2 : ℝ)) ?_ ?_
      · exact (hf.sub hg).norm.aestronglyMeasurable
      · filter_upwards [] with x
        dsimp [f, g]
        have hcalc : ‖Complex.exp (s * x * Complex.I) -
            Complex.exp (t * x * Complex.I)‖ ≤ 2 := by
          calc
            ‖Complex.exp (s * x * Complex.I) - Complex.exp (t * x * Complex.I)‖
                ≤ ‖Complex.exp (s * x * Complex.I)‖ +
                  ‖Complex.exp (t * x * Complex.I)‖ := norm_sub_le _ _
            _ = 2 := by norm_num [Complex.norm_exp]
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hcalc
    have hboundInt : Integrable
        (fun x : ℝ => δ * R + 2 * (Kᶜ).indicator (fun _ => (1 : ℝ)) x) (μ n) := by
      exact (integrable_const _).add
        ((integrable_const (1 : ℝ)).indicator hK.isClosed.isOpen_compl.measurableSet |>.const_mul 2)
    have hpoint : ∀ x, ‖f x - g x‖ ≤ δ * R +
        2 * (Kᶜ).indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ K
      · have hxR : |x| ≤ R := by
          have hx' := hKR hx
          simpa [Metric.mem_closedBall, Real.dist_eq] using hx'
        have hexp : ‖Complex.exp ((s * x) * Complex.I) -
            Complex.exp ((t * x) * Complex.I)‖ ≤ |(s - t) * x| := by
          have hfactor : Complex.exp ((s * x) * Complex.I) -
              Complex.exp ((t * x) * Complex.I) =
              Complex.exp ((t * x) * Complex.I) *
                (Complex.exp (((s - t) * x) * Complex.I) - 1) := by
            rw [show (s * x) * Complex.I =
              (t * x) * Complex.I + ((s - t) * x) * Complex.I by ring,
              Complex.exp_add]
            ring
          rw [hfactor, norm_mul]
          have hexpnorm : ‖Complex.exp ((t * x) * Complex.I)‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [hexpnorm, one_mul]
          have htrig := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - t) * x)
          calc
            ‖Complex.exp (((s - t) * x) * Complex.I) - 1‖ =
                ‖Complex.exp (Complex.I * (((s - t) * x : ℝ) : ℂ)) - 1‖ := by
              congr 2
              rw [mul_comm]
              push_cast
              rfl
            _ ≤ ‖(s - t) * x‖ := by
              exact htrig
            _ = |(s - t) * x| := by simp [Real.norm_eq_abs]
        have hst' : |s - t| < δ := by
          simpa [Real.dist_eq] using hst
        have hnum : |(s - t) * x| ≤ δ * R := by
          rw [abs_mul]
          exact (mul_le_mul (le_of_lt hst') hxR (abs_nonneg x) (by positivity)).trans_eq
            (by ring)
        simpa [f, g, hx] using le_trans hexp hnum
      · have htwo : ‖f x - g x‖ ≤ 2 := by
          calc
            ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
            _ = 2 := by norm_num [f, g, Complex.norm_exp]
        have hind : (Kᶜ).indicator (fun _ => (1 : ℝ)) x = 1 := by
          simp [Set.indicator, hx]
        rw [hind]
        have hδRnonneg : 0 ≤ δ * R := mul_nonneg hδ.le hR.le
        linarith
    have hcharSub : charFun (μ n) s - charFun (μ n) t =
        ∫ x, f x - g x ∂(μ n) := by
      rw [charFun_apply_real, charFun_apply_real, ← integral_sub hf hg]
    have hnorm : dist (charFun (μ n) s) (charFun (μ n) t) ≤
        ∫ x, ‖f x - g x‖ ∂(μ n) := by
      rw [dist_eq_norm, hcharSub]
      exact norm_integral_le_integral_norm _
    have hInt := integral_mono_ae hdiffInt hboundInt (ae_of_all _ hpoint)
    have hKtailENN : (μ n) Kᶜ ≤ ENNReal.ofReal (ε / 8) := hTail (μ n) ⟨n, rfl⟩
    have hKtail : ((μ n).real Kᶜ) ≤ ε / 8 := by
      calc
        ((μ n) Kᶜ).toReal ≤ (ENNReal.ofReal (ε / 8)).toReal :=
          ENNReal.toReal_mono (by simp) hKtailENN
        _ = ε / 8 := ENNReal.toReal_ofReal (by positivity)
    have hbound : ∫ x, δ * R + 2 * (Kᶜ).indicator (fun _ => (1 : ℝ)) x ∂μ n
        ≤ δ * R + ε / 4 := by
      have hind : ∫ x, (Kᶜ).indicator (fun _ => (1 : ℝ)) x ∂μ n =
          (μ n).real Kᶜ :=
        integral_indicator_one hK.isClosed.isOpen_compl.measurableSet
      have hIndicator : Integrable
          (fun x : ℝ => (Kᶜ).indicator (fun _ => (1 : ℝ)) x) (μ n) :=
        (integrable_const (1 : ℝ)).indicator
          hK.isClosed.isOpen_compl.measurableSet
      have hSecondInt : Integrable
          (fun x : ℝ => (2 : ℝ) • (Kᶜ).indicator (fun _ => (1 : ℝ)) x) (μ n) :=
        hIndicator.const_mul (2 : ℝ)
      rw [show (fun x : ℝ => δ * R + 2 * (Kᶜ).indicator (fun _ => (1 : ℝ)) x) =
        fun x => (δ * R) + (2 : ℝ) • (Kᶜ).indicator (fun _ => (1 : ℝ)) x by
          funext x
          simp [smul_eq_mul]]
      rw [integral_add (integrable_const _) hSecondInt, integral_const]
      rw [integral_smul, hind]
      simp only [smul_eq_mul]
      have hUniv : (μ n).real Set.univ = 1 := by simp [Measure.real_def]
      rw [hUniv]
      have hTailReal : ((μ n) Kᶜ).toReal ≤ ε / 8 := by
        simpa [Measure.real_def] using hKtail
      nlinarith [hTailReal]
    calc
      dist (charFun (μ n) s) (charFun (μ n) t) ≤ ∫ x, ‖f x - g x‖ ∂μ n := hnorm
      _ ≤ ∫ x, δ * R + 2 * (Kᶜ).indicator (fun _ => (1 : ℝ)) x ∂μ n := hInt
      _ ≤ δ * R + ε / 4 := hbound
      _ < ε := by
        have hδR : δ * R < ε / 4 := by
          dsimp [δ]
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ (by positivity : 0 < 4 * (R + 1))).2
          nlinarith [hε, hR]
        linarith
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs n
  exact hUε (hEqui n t s (by simpa [dist_comm] using hs))

/-- If probability measures converge weakly, their characteristic functions
converge uniformly on every compact frequency set. -/
theorem tendstoUniformlyOn_charFun_of_tendsto
    {μ : ℕ → Measure ℝ} {μLimit : Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure μLimit]
    {K : Set ℝ} (hK : IsCompact K)
    (hcf : ∀ t : ℝ, Tendsto (fun n => charFun (μ n) t) atTop
      (nhds (charFun μLimit t))) :
    TendstoUniformlyOn (fun n t => charFun (μ n) t) (charFun μLimit) atTop K := by
  have htight : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_of_tendsto_charFun
      (MeasureTheory.continuous_charFun (μ := μLimit)).continuousAt hcf
  have hEqui := equicontinuous_charFun_of_isTightMeasureSet htight
  let F : ℕ → K → ℂ := fun n x => charFun (μ n) x
  let f : K → ℂ := fun x => charFun μLimit x
  have hFEqui : Equicontinuous F := by
    exact (equicontinuous_restrict_iff (fun n t => charFun (μ n) t)).2
      (hEqui.equicontinuousOn K)
  have hPoint : Tendsto F atTop (nhds f) := by
    rw [tendsto_pi_nhds]
    intro x
    exact hcf x
  have hUniform : TendstoUniformly F f atTop := by
    have hcompact : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let hcompact := hcompact
    have h := (hFEqui.tendsto_uniformFun_iff_pi atTop f).2 hPoint
    exact UniformFun.tendsto_iff_tendstoUniformly.mp h
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  change TendstoUniformly F f atTop
  exact hUniform

end MeasureTheory

end
