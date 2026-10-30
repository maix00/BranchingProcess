/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Analysis.Fourier.PositiveDefinite
import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Fejér approximation in the Bochner proof

This internal proof stage defines the inverse-Fourier density
`ρψ(x) = (2π)⁻¹ Re ∫ ψ(u) exp(-ixu) du` and its triangular truncations
`Fₙ(x) = (2π)⁻¹ Re ∫_{-n}^{n} ψ(u) exp(-ixu)(1 - |u|/n) du`.
For continuous integrable positive-definite `ψ`, it proves `Fₙ(x) ≥ 0` and
`Fₙ(x) → ρψ(x)`, which gives nonnegativity of the inverse-Fourier density.

This file contains only package-internal proof support for
`Analysis.Fourier.Bochner.Theorem`; it has no public declarations.

## Internal proof declarations

- The private `inverseFourierDensity` is
  $\rho_\psi(x)=(2\pi)^{-1}\operatorname{Re}\int_{\mathbb R}\psi(u)e^{-ixu}\,du$.
- The private `fejerApproximant` is its triangular truncation
  $F_n(x)=(2\pi)^{-1}\operatorname{Re}\int_{-n}^{n}\psi(u)e^{-ixu}(1-|u|/n)\,du$.
- `fejerApproximant_nonneg` and `tendsto_fejerApproximant` prove
  $F_n(x)\ge 0$ and $F_n(x)\to\rho_\psi(x)$ for continuous integrable
  positive-definite $\psi$.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

private lemma intervalIntegral_eq_zero_of_forall_eq_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : ∀ t, t ∈ Set.uIoo a b → f t = 0) :
    ∫ t in a..b, f t = 0 := by
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_of_le hab ▸ ht)
  · rw [intervalIntegral.integral_symm, neg_eq_zero,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_comm a b ▸ Set.uIoo_of_le hab.le ▸ ht)

/-! ### Helper lemmas -/

/-- The inverse Fourier density of an L¹ function, using the probabilist convention:
`ρ(x) = (1/(2π)) · Re(∫ ψ(u) e^{-ixu} du)`.

When `ψ` is a PD function with `ψ(0) = 1`, this gives the probability density whose
characteristic function is `ψ`. -/
private noncomputable def inverseFourierDensity (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ u, ψ u * exp (-(↑x * ↑u * I))).re

/-- The Fejér approximant: the tapered inverse Fourier transform with triangle window.
`F_N(x) = (1/2π) ∫_{-N}^{N} ψ(u) e^{-ixu} (1 - |u|/N) du`.

For continuous `ψ` and `N > 0`, the tent identity rewrites this as
`(1/(2πN)) ∫_0^N ∫_0^N Re (ψ (s - t) e^{-ix(s-t)}) dt ds`. -/
private noncomputable def fejerApproximant (ψ : ℝ → ℂ) (N : ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ u in Set.Icc (-N) N,
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re

/-- The product of a PD function `ψ` and `u ↦ exp(-ixu)` is PD. -/
private lemma isPositiveDefinite_mul_exp (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ) (x : ℝ) :
    IsPositiveDefinite (fun u => ψ u * exp (-(↑x * ↑u * I))) := by
  exact hpd.mul (IsPositiveDefinite.exp_neg_ofReal_mul x)

/-- PD Riemann sums R_m = (h²/N) * Re(∑ᵢ ∑ⱼ g((i-j)h)) are non-negative. -/
private lemma riemannSum_nonneg_of_pd (g : ℝ → ℂ) (hg_pd : IsPositiveDefinite g)
    (N : ℝ) (hN : 0 < N) (m : ℕ) :
    0 ≤ (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re := by
  apply mul_nonneg
  · exact div_nonneg (sq_nonneg _) hN.le
  · have h := hg_pd (m + 1)
      (fun i => (i : ℝ) * (N / ((m : ℝ) + 1))) (fun _ => 1)
    simp only [map_one, one_mul] at h
    exact (Complex.nonneg_iff.mp h).1

set_option maxHeartbeats 800000 in
/-- The Fejér tent integral equals `(1/N) * ∫_0^N ∫_0^N Re(g(s-t)) ds dt` via
Fubini and the change of variables `u = s - t`. -/
private lemma tent_integral_eq_fubini (g : ℝ → ℂ) (hg_cont : Continuous g)
    (N : ℝ) (hN : 0 < N) :
    (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
    (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, (g (s - t)).re := by
  -- Step 1: LHS = ∫ in Icc(-N,N), (g u).re * (1-|u|/N)
  have hf_int : Integrable (fun u => g u * (1 - ↑(|u| / N : ℝ) : ℂ))
      (volume.restrict (Set.Icc (-N) N)) :=
    (hg_cont.mul (continuous_const.sub
      (continuous_ofReal.comp
        ((continuous_abs.comp continuous_id).div_const N)))).continuousOn.integrableOn_Icc
  have hLHS : (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
      ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
    calc (∫ u in Set.Icc (-N) N,
            g u * (1 - ↑(|u| / N))).re
        = ∫ u in Set.Icc (-N) N,
            (g u * (1 - ↑(|u| / N))).re :=
            (integral_re hf_int).symm
      _ = ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
            congr 1; ext u
            have : (1 : ℂ) - ↑(|u| / N) = ↑((1 : ℝ) - |u| / N) := by push_cast; ring
            rw [this, re_mul_ofReal]
  rw [hLHS]
  -- Step 2: ∫∫ F = ∫_{-N}^N (g u).re * (N-|u|) (Fubini + change of variables)
  set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
  have hF_cts : Continuous F.uncurry :=
    (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
  have hfub : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
      ∫ u in Set.Icc (-N) N, (g u).re * (N - |u|) := by
    -- Build product integrability
    have hint : Integrable F.uncurry
        ((volume.restrict (Set.Icc 0 N)).prod (volume.restrict (Set.Icc 0 N))) := by
      rw [Measure.prod_restrict]
      exact hF_cts.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    -- Fubini swap: ∫_s ∫_t F = ∫_t ∫_s F
    have hswap : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
        ∫ t in Set.Icc 0 N, ∫ s in Set.Icc 0 N, F s t :=
      integral_integral_swap hint
    rw [hswap]
    -- Inner integral: ∫_s F(s,t) = ∫_{-t}^{N-t} (g u).re via s → u=s-t
    have hinner2 : ∀ t ∈ Set.Icc (0:ℝ) N, ∫ s in Set.Icc 0 N, F s t =
        ∫ u in (-t)..(N - t), (g u).re := by
      intro t _
      simp only [F]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le,
          intervalIntegral.integral_comp_sub_right (fun u => (g u).re) t]
      congr 1; ring
    rw [setIntegral_congr_fun measurableSet_Icc hinner2]
    -- Extend inner interval integral to Icc(-N,N) with indicator, then Fubini
    have hlhs_ext : ∫ t in Set.Icc 0 N, ∫ u in (-t)..(N - t), (g u).re =
        ∫ t in (0 : ℝ)..N, ∫ u in Set.Icc (-N) N,
          (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hN.le] at ht
      have hsubset : Set.Icc (-t) (N - t) ⊆ Set.Icc (-N) N :=
        fun u ⟨h1, h2⟩ => ⟨by linarith [ht.2], by linarith [ht.1]⟩
      -- Convert interval integral to set integral then extend
      show ∫ u in (-t)..(N - t), (g u).re =
        ∫ u in Set.Icc (-N) N, (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u
      rw [intervalIntegral.integral_of_le (show -t ≤ N - t by linarith [ht.1]),
          ← integral_Icc_eq_integral_Ioc]
      conv_rhs =>
        arg 2; ext u
        rw [show (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
            Set.indicator (Set.Icc (-t) (N - t)) (fun u => (g u).re) u from by
          simp [Set.indicator_apply]]
      rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsubset]
    rw [hlhs_ext]
    -- Fubini swap for the extended integral
    have hmeas_ind : Measurable (fun p : ℝ × ℝ =>
        (g p.2).re * Set.indicator (Set.Icc (-p.1) (N - p.1)) 1 p.2) :=
      ((Complex.continuous_re.comp hg_cont).measurable.comp measurable_snd).mul
        (Measurable.indicator measurable_const
          ((measurableSet_le (measurable_neg.comp measurable_fst) measurable_snd).inter
           (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))))
    -- Integrability: bound by |g u| which is integrable on Icc(-N,N)
    have h_re_int : Integrable (fun u => (g u).re)
        (volume.restrict (Set.Icc (-N) N)) :=
      (Complex.continuous_re.comp hg_cont).continuousOn.integrableOn_Icc
    have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 N)) :=
      ⟨by simp [Real.volume_uIoc, abs_of_nonneg hN.le]⟩
    have hint_prod : Integrable
        (uncurry fun t u => (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u)
        ((volume.restrict (Set.uIoc 0 N)).prod
         (volume.restrict (Set.Icc (-N) N))) :=
      (h_re_int.comp_snd (volume.restrict (Set.uIoc 0 N))).mono
        hmeas_ind.aestronglyMeasurable (ae_of_all _ fun ⟨t, u⟩ => by
          simp only [uncurry]
          calc ‖(g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u‖
              ≤ ‖(g u).re‖ * ‖Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u‖ :=
                norm_mul_le _ _
            _ ≤ ‖(g u).re‖ * 1 := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                simp [Set.indicator_apply]; split_ifs <;> simp
            _ = ‖(g u).re‖ := mul_one _)
    rw [intervalIntegral_integral_swap hint_prod]
    -- Compute inner integral ∫ t in 0..N, Re(g u) * indicator(t ∈ Icc(-t,N-t))
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    have huN_bound : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    -- indicator swap: u ∈ Icc(-t,N-t) ↔ t ∈ Icc(-u,N-u)
    have hcond_swap : ∀ t : ℝ,
        Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u =
        Set.indicator (Set.Icc (-u) (N - u)) 1 t := fun t => by
      simp only [Set.indicator_apply, Set.mem_Icc]
      exact ite_congr
        (propext ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
                 fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩)
        (fun _ => rfl) (fun _ => rfl)
    rw [show ∫ t in (0 : ℝ)..N,
            (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
        (g u).re * ∫ t in (0 : ℝ)..N,
            Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u from
      intervalIntegral.integral_const_mul _ _]
    congr 1
    simp_rw [hcond_swap]
    -- Compute ∫ t in 0..N, 1_{Icc(-u,N-u)} t = N - |u|
    rcases le_or_gt u 0 with hu0 | hu0
    · -- u ≤ 0: interval is [-u, N] ∩ [0,N] = [-u, N], length = N+u = N-|u|
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (-u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (-u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(-u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [hu0])] at ht
            simp [Set.mem_Icc,
                  show ¬(-u ≤ t) from by linarith [ht.2]]]
      have hnu_le_N : -u ≤ N := by
        rw [abs_of_nonpos hu0] at huN_bound; linarith
      rw [show ∫ t in (-u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (-u)..N, (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le hnu_le_N] at ht
            simp [Set.mem_Icc, ht.1,
                  show t ≤ N - u from by linarith [hu0, ht.2]]]
      simp [intervalIntegral.integral_const, abs_of_nonpos hu0]
    · -- u > 0: interval is [-u, N-u] ∩ [0,N] = [0, N-u], length = N-u = N-|u|
      have huN : u ≤ N := by
        rw [abs_of_pos hu0] at huN_bound; exact huN_bound
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (N - u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (N - u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(N - u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (0 : ℝ)..(N - u), (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le (by linarith [huN])] at ht
            simp [Set.mem_Icc,
                  show -u ≤ t from by linarith [ht.1, hu0.le], ht.2]]
      rw [show ∫ t in (N - u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [huN])] at ht
            simp [Set.mem_Icc, show ¬(t ≤ N - u) from by
              linarith [ht.1]]]
      simp [intervalIntegral.integral_const, abs_of_pos hu0]
  -- Step 3: Combine LHS with hfub
  rw [hfub, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  have huN_abs : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  field_simp [hN.ne']

set_option maxHeartbeats 800000 in
/-- 2D Riemann sum convergence: for a uniformly continuous function F on [0,N]²,
the sum h² * ∑ᵢ ∑ⱼ F(ih, jh) converges to ∫∫ F as h → 0. -/
private lemma tendsto_riemannSum_of_uniformContinuousOn
    (F : ℝ → ℝ → ℝ) (N : ℝ) (hN : 0 < N)
    (hF_cts : Continuous F.uncurry)
    (hF_ucont : UniformContinuousOn F.uncurry
        (Set.Icc 0 N ×ˢ Set.Icc 0 N)) :
    Tendsto (fun m : ℕ => (N / ((m : ℝ) + 1)) ^ 2 *
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1))))
      atTop (𝓝 (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at hF_ucont
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_ucont (ε / 2 / N ^ 2) (by positivity)
  have hδ' : 0 < δ / Real.sqrt 2 := by positivity
  refine ⟨⌈N / (δ / Real.sqrt 2)⌉₊, fun m hm => ?_⟩
  set h := N / ((m : ℝ) + 1) with hh_def
  have hh_pos : (0 : ℝ) < h := div_pos hN (by positivity)
  have hh_small : h < δ / Real.sqrt 2 := by
    have hM_le : (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hM_pos : (0 : ℝ) < ⌈N / (δ / Real.sqrt 2)⌉₊ := by
      exact_mod_cast Nat.ceil_pos.mpr (by positivity)
    calc h = N / ((m : ℝ) + 1) := hh_def
        _ < N / (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) := by
            apply div_lt_div_of_pos_left hN (by exact_mod_cast hM_pos)
            linarith
        _ ≤ N / (N / (δ / Real.sqrt 2)) := by
            apply div_le_div_of_nonneg_left hN.le (by positivity)
            exact_mod_cast Nat.le_ceil _
        _ = δ / Real.sqrt 2 := by field_simp [hN.ne']
  -- Split ∫∫ F into (m+1)² boxes
  have hbox_split : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
        ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t := by
    have hN_eq : N = (m + 1 : ℝ) * h := by push_cast [hh_def]; field_simp
    -- Continuity of s ↦ ∫_t F s t (needed for outer split integrability)
    have hφ_cont : Continuous (fun s => ∫ t in Set.Icc 0 N, F s t) :=
      continuous_parametric_integral_of_continuous hF_cts isCompact_Icc
    -- Helper: split ∫ in Icc 0 N into m+1 sub-intervals
    have h_Icc_split : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Set.Icc 0 N) →
        ∫ u in Set.Icc 0 N, φ u =
        ∑ i : Fin (m + 1), ∫ u in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h), φ u := by
      intro φ hφ
      have h_a_def : ∀ k : ℕ, (k : ℝ) * h = (fun k : ℕ => (k : ℝ) * h) k := fun k => rfl
      rw [show (0 : ℝ) = (↑(0 : ℕ)) * h from by simp, hN_eq,
          show (↑m + (1 : ℝ)) * h = (↑(m + 1 : ℕ) : ℝ) * h from by push_cast; ring,
          integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by push_cast; nlinarith [hh_pos])]
      rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun k : ℕ => (k : ℝ) * h) (Nat.zero_le _)
        (fun k hk =>
          (hφ.mono (Set.Icc_subset_Icc (by positivity)
            (by rw [hN_eq]; apply mul_le_mul_of_nonneg_right _ hh_pos.le
                have : k + 1 ≤ m + 1 := hk.2
                exact_mod_cast this))).intervalIntegrable_of_Icc
            (by push_cast; linarith [hh_pos, hk.1]))]
      rw [Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range]
      congr 1; ext i; push_cast
      rw [intervalIntegral.integral_of_le (by nlinarith [hh_pos]),
          ← integral_Icc_eq_integral_Ioc]
    -- Step 1: split outer integral
    rw [h_Icc_split _ hφ_cont.continuousOn]
    -- Step 2: for each i, split inner integral and pull ∑ outside
    congr 1; ext i
    rw [show ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc 0 N, F s t =
        ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
          ∑ j : Fin (m + 1), ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
          F s t from by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      exact h_Icc_split (fun t => F s t)
        (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn]
    rw [integral_finsetSum (Finset.univ : Finset (Fin (m + 1))) (fun (j : Fin (m + 1)) _ =>
      (continuous_parametric_integral_of_continuous hF_cts
        (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc)]
  -- Bound the error
  rw [Real.dist_eq, hbox_split]
  calc |((N / ((m : ℝ) + 1)) ^ 2 * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          F ((i : ℝ) * h) ((j : ℝ) * h)) -
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
          ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t|
      = |∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          (h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
           ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
           ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t)| := by
        congr 1
        simp_rw [← hh_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          |h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
           ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
           ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin (m + 1), ∑ _j : Fin (m + 1), h ^ 2 * (ε / 2 / N ^ 2) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have hile : (i : ℝ) * h ≤ ((i : ℝ) + 1) * h := by nlinarith [hh_pos]
        have hjle : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith [hh_pos]
        have hN_eq' : N = (↑m + 1) * h := by rw [hh_def]; field_simp
        have hi_bound : ((i : ℝ) + 1) * h ≤ N := by
          rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
          have := i.2; exact_mod_cast this
        have hj_bound : ((j : ℝ) + 1) * h ≤ N := by
          rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
          have := j.2; exact_mod_cast this
        have hi_nn : (0 : ℝ) ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
        have hj_nn : (0 : ℝ) ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
        have hint_const_j : IntegrableOn (fun _ => F ((i : ℝ) * h) ((j : ℝ) * h))
            (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) :=
          integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
        have hint_F_inner : ∀ s : ℝ, IntegrableOn (fun t => F s t)
            (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) := fun s =>
          (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
        have hint_const_i : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              F ((i : ℝ) * h) ((j : ℝ) * h))
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
          integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
        have hint_F_outer : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t)
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
          (continuous_parametric_integral_of_continuous hF_cts
            (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc
        -- Write h²*F_const - ∫∫F = ∫∫(F_const - F s t) via linearity
        have heq : h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t =
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
            (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t) := by
          rw [show h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) =
              ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              F ((i : ℝ) * h) ((j : ℝ) * h) from by
            simp only [setIntegral_const, smul_eq_mul,
              Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
            ring]
          rw [← integral_sub hint_const_i hint_F_outer]
          congr 1; ext s
          rw [← integral_sub hint_const_j (hint_F_inner s)]
        rw [heq]
        -- Bound |∫∫(F_const - F s t)| ≤ ∫∫ |F_const - F s t| ≤ ∫∫(ε/2/N²) = h²*(ε/2/N²)
        have hint_diff_outer : IntegrableOn
            (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t))
            (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) := by
          have := hint_const_i.sub hint_F_outer
          simp only [integral_sub hint_const_j (hint_F_inner _)] at this ⊢
          exact this
        calc |∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)|
            ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ‖∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)‖ :=
                by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
          _ ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              ε / 2 / N ^ 2 := by
              apply setIntegral_mono_on hint_diff_outer.norm
                (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                measurableSet_Icc
              intro s hs
              apply le_trans (norm_integral_le_integral_norm _)
              apply setIntegral_mono_on (hint_const_j.sub (hint_F_inner s)).norm
                (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                measurableSet_Icc
              intro t ht
              simp only [Pi.sub_apply, Real.norm_eq_abs]
              rw [show |F ((i : ℝ) * h) ((j : ℝ) * h) - F s t| =
                  dist (uncurry F ((i : ℝ) * h, (j : ℝ) * h))
                       (uncurry F (s, t)) from by
                simp [uncurry, Real.dist_eq]]
              apply le_of_lt
              apply hδ
              · exact ⟨⟨hi_nn, by linarith [hi_bound]⟩,
                      ⟨hj_nn, by linarith [hj_bound]⟩⟩
              · exact ⟨⟨hi_nn.trans hs.1, hs.2.trans (by linarith [hi_bound])⟩,
                      ⟨hj_nn.trans ht.1, ht.2.trans (by linarith [hj_bound])⟩⟩
              · rw [Prod.dist_eq]
                have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
                have hsqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
                  rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
                calc max (dist ((i : ℝ) * h) s) (dist ((j : ℝ) * h) t)
                    ≤ Real.sqrt 2 * h := by
                      apply max_le
                      · rw [Real.dist_eq, abs_le]
                        exact ⟨by nlinarith [hs.2, hsqrt2_ge_one],
                               by nlinarith [hs.1, hsqrt2_pos]⟩
                      · rw [Real.dist_eq, abs_le]
                        exact ⟨by nlinarith [ht.2, hsqrt2_ge_one],
                               by nlinarith [ht.1, hsqrt2_pos]⟩
                  _ < δ := by
                      have : Real.sqrt 2 * h < Real.sqrt 2 * (δ / Real.sqrt 2) :=
                        mul_lt_mul_of_pos_left hh_small hsqrt2_pos
                      rwa [mul_div_cancel₀ _ hsqrt2_pos.ne'] at this
          _ = h ^ 2 * (ε / 2 / N ^ 2) := by
              simp only [setIntegral_const, smul_eq_mul,
                Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
              ring
    _ = ε / 2 := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hm1_pos : (0 : ℝ) < ↑m + 1 := by positivity
        rw [hh_def]
        push_cast
        field_simp [hm1_pos.ne']
    _ < ε := by linarith

set_option maxHeartbeats 800000 in
private lemma fejerApproximant_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (N : ℝ) (hN : 0 < N) (x : ℝ) : 0 ≤ fejerApproximant ψ N x := by
  -- Direct proof via PD Riemann sums, bypassing the double integral.
  -- Define g(u) = ψ(u) * exp(-ixu), which is PD and continuous.
  -- The Fejér approximant = (1/(2π)) * (∫_{[-N,N]} g(u)(1-|u|/N) du).re.
  -- The Riemann sum S_m = h * ∑_{k} g(kh)(1-|kh|/N) (h = N/m) equals
  -- (N/m²) * Re(∑ᵢ ∑ⱼ g((i-j)N/m)) which is ≥ 0 by PD (with cᵢ = 1).
  -- Since S_m → ∫ g(u)(1-|u|/N) du by 1D Riemann sum convergence, the integral is ≥ 0.
  unfold fejerApproximant
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos |>.le
  · -- Need: (∫ u in Icc(-N,N), g(u)(1-|u|/N)).re ≥ 0
    set g : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I)) with hg_def
    -- g is PD (product of ψ and exp(-ix·) which is PD)
    have hg_pd : IsPositiveDefinite g := isPositiveDefinite_mul_exp ψ hpd x
    -- g is continuous
    have hg_cont : Continuous g :=
      hψc.mul (((continuous_const.mul continuous_ofReal).mul continuous_const).neg.cexp)
    -- Step A: Define the approximating sequence.
    -- R_m = (N/(m+1)²) * Re(∑ᵢ ∑ⱼ g((i-j)*N/(m+1))) for m : ℕ.
    -- This equals the Riemann sum h * ∑_k g(kh)(1-|kh|/N) where h = N/(m+1).
    set R : ℕ → ℝ := fun m =>
      (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re
    -- Step B: Each R_m ≥ 0 by PD (with cᵢ = 1)
    have hR_nn : ∀ m : ℕ, 0 ≤ R m := fun m => riemannSum_nonneg_of_pd g hg_pd N hN m
    -- Step C: R_m converges to (∫ g(u)(1-|u|/N)).re as m → ∞
    -- This is Riemann sum convergence for the continuous function
    -- u ↦ g(u)(1-|u|/N) on the compact interval [-N,N].
    -- The key combinatorial identity is:
    --   (h/N) * ∑_{i,j} g((i-j)h) = h * ∑_k g(kh)(1-|kh|/N)
    -- where the sum over k ranges over |k| ≤ m, and h = N/(m+1).
    -- This identity follows from counting pairs (i,j) with i-j = k:
    --   #{(i,j) ∈ [0,m]² : i-j = k} = m+1-|k| for |k| ≤ m.
    have hR_tendsto : Tendsto R atTop (𝓝 (∫ u in Set.Icc (-N) N,
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re) := by
      -- Strategy: define F(s,t) = Re(g(s-t)) on [0,N]².
      -- Then R m = (1/N) * h² * ∑_{i,j} F(i*h, j*h) and
      -- target = (1/N) * ∫_0^N ∫_0^N F s t dt ds (via Fubini + change of variables).
      -- Since F is uniformly continuous on [0,N]², the 2D Riemann sum converges to ∫∫ F.
      set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
      have hF_cts : Continuous F.uncurry :=
        (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
      have hF_ucont : UniformContinuousOn F.uncurry
          (Set.Icc 0 N ×ˢ Set.Icc 0 N) :=
        (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
          hF_cts.continuousOn
      -- R m = (1/N) * h² * ∑_{i,j} F(i*h, j*h)
      have hR_form : ∀ m : ℕ, R m = (1 / N) * (N / ((m : ℝ) + 1)) ^ 2 *
          (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) := by
        intro m
        simp only [R, F]
        rw [show (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re =
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            (g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re from by
          simp [Complex.re_sum]]
        ring
      -- target = (1/N) * ∫_0^N ∫_0^N F (via Fubini + tent identity)
      have htarget_eq : (∫ u in Set.Icc (-N) N,
          ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re =
          (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t :=
        tent_integral_eq_fubini g hg_cont N hN
      rw [htarget_eq]
      -- Step C3: 2D Riemann sum convergence via ε-δ with uniform continuity
      suffices hS : Tendsto (fun m : ℕ => (N / ((m : ℝ) + 1)) ^ 2 *
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1))))
          atTop (𝓝 (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t)) by
        have hR_eq : R = fun (m : ℕ) => (1 / N) * ((N / ((m : ℝ) + 1)) ^ 2 *
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) :=
          funext (fun m => by rw [hR_form]; ring)
        rw [hR_eq]
        exact (tendsto_const_nhds (x := 1 / N)).mul hS
      exact tendsto_riemannSum_of_uniformContinuousOn F N hN hF_cts hF_ucont
    -- Step D: Conclude by ge_of_tendsto
    exact ge_of_tendsto hR_tendsto (Eventually.of_forall hR_nn)


/-- The Fejér approximants converge pointwise to the inverse Fourier density, under
the integrability assumption on `ψ`. By DCT: the tapered integrand converges to the
un-tapered integrand, dominated by `‖ψ‖ ∈ L¹`. -/
private lemma tendsto_fejerApproximant (ψ : ℝ → ℂ) (hI : Integrable ψ volume) (x : ℝ) :
    Tendsto (fun n : ℕ => fejerApproximant ψ (↑n + 1) x)
      atTop (𝓝 (inverseFourierDensity ψ x)) := by
  unfold fejerApproximant inverseFourierDensity
  -- It suffices to show the .re parts converge, then multiply by the constant.
  apply Filter.Tendsto.const_mul
  apply Complex.continuous_re.continuousAt.tendsto.comp
  -- Rewrite set integral as full integral with indicator.
  set f : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I))
  set F : ℕ → ℝ → ℂ := fun n u =>
    (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
      (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u
  have hset_eq : ∀ n : ℕ, ∫ u in Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1),
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) =
      ∫ u, F n u := by
    intro n; rw [← integral_indicator (measurableSet_Icc)]
  simp_rw [hset_eq]
  -- Apply DCT
  apply tendsto_integral_of_dominated_convergence (fun u => ‖ψ u‖)
  · -- F n is AEStronglyMeasurable
    intro n
    apply AEStronglyMeasurable.indicator _ measurableSet_Icc
    apply AEStronglyMeasurable.mul
    · exact (hI.1.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
        continuous_const).neg.cexp).aestronglyMeasurable)
    · exact (continuous_const.sub (continuous_ofReal.comp
        (continuous_abs.div_const _))).aestronglyMeasurable
  · exact hI.norm
  · -- ‖F n u‖ ≤ ‖ψ u‖
    intro n; apply ae_of_all; intro u
    simp only [F]
    by_cases hu : u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)
    · rw [Set.indicator_of_mem hu, norm_mul, norm_mul]
      have hN_pos : (0 : ℝ) < ↑n + 1 := by positivity
      have hu_abs_le : |u| ≤ ↑n + 1 :=
        abs_le.mpr ⟨by linarith [(Set.mem_Icc.mp hu).1], (Set.mem_Icc.mp hu).2⟩
      have hfrac_le : |u| / (↑n + 1) ≤ 1 := (div_le_one hN_pos).mpr hu_abs_le
      have hfrac_nn : 0 ≤ 1 - |u| / (↑n + 1) := by linarith
      calc ‖ψ u‖ * ‖exp (-(↑x * ↑u * I))‖ * ‖(1 - ↑(|u| / (↑n + 1)) : ℂ)‖
          ≤ ‖ψ u‖ * 1 * 1 := by
            gcongr
            · rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I]
            · -- ‖1 - ↑(|u|/(n+1))‖ ≤ 1
              calc ‖(1 : ℂ) - ↑(|u| / (↑n + 1))‖
                  = ‖(↑(1 - |u| / (↑n + 1)) : ℂ)‖ := by push_cast; ring_nf
                _ = |1 - |u| / (↑n + 1)| := Complex.norm_real _
                _ = 1 - |u| / (↑n + 1) := abs_of_nonneg hfrac_nn
                _ ≤ 1 := by linarith [div_nonneg (abs_nonneg u) (le_of_lt hN_pos)]
        _ = ‖ψ u‖ := by ring
    · rw [Set.indicator_apply, ite_eq_right hu, norm_zero]; exact norm_nonneg _
  · -- F n u → f u pointwise a.e.
    apply ae_of_all; intro u
    simp only [F]
    -- Eventually u ∈ Icc(-(n+1), n+1)
    have hmem : ∀ᶠ n : ℕ in atTop, u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1) := by
      rw [Filter.eventually_atTop]
      exact ⟨⌈|u|⌉₊, fun n hn => by
        have hle : |u| ≤ ↑n + 1 := by
          calc |u| ≤ ↑⌈|u|⌉₊ := Nat.le_ceil |u|
            _ ≤ ↑n := Nat.cast_le.mpr hn
            _ ≤ ↑n + 1 := le_add_of_nonneg_right zero_le_one
        exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩
    -- Eventually the indicator is just the function value
    have heq : ∀ᶠ n : ℕ in atTop,
        (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
          (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u =
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) :=
      hmem.mono fun n hn => Set.indicator_of_mem hn _
    apply Tendsto.congr' (EventuallyEq.symm heq)
    -- ψ(u) * exp(...) * (1 - |u|/(n+1)) → ψ(u) * exp(...) as (1 - |u|/(n+1)) → 1
    have h_frac : Tendsto (fun n : ℕ => |u| / ((↑n : ℝ) + 1)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h_window : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => (↑(|u| / ((↑n : ℝ) + 1)) : ℂ)) atTop (𝓝 0) := by
        rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
        exact (Complex.continuous_ofReal.tendsto 0).comp h_frac
      have h1 : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop
          (𝓝 ((1 : ℂ) - 0)) := (tendsto_const_nhds (x := (1 : ℂ))).sub hc
      simp only [sub_zero] at h1
      exact h1
    conv_rhs => rw [show ψ u * exp (-(↑x * ↑u * I)) =
      ψ u * exp (-(↑x * ↑u * I)) * 1 from (mul_one _).symm]
    exact tendsto_const_nhds.mul h_window


end ProbabilityTheory
