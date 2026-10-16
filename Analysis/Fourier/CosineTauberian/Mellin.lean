/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Fourier.CosineTauberian.Kernel
public import Analysis.Fourier.CosineTauberian.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mellin positivity for the cosine Tauberian kernel

This module identifies the signed Mellin moment of the inverse cosine kernel
by integrating its already established Fourier profile identity against a
power weight. In particular, it does not assume that the kernel is pointwise
nonnegative.
-/

open MeasureTheory Set
open scoped Interval RealInnerProductSpace

@[expose] public section

namespace Analysis.Fourier.CosineTauberian

noncomputable def cosineTauberianMellinWeight (α y : ℝ) : ℝ :=
  (1 - Real.cos y) * y ^ (-1 - α)

noncomputable def cosineTauberianCosineMoment (α : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α y

noncomputable def cosineTauberianMellinMoment (α : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ α * cosineTauberianKernel s

noncomputable def cosineTauberianProfileGapWeight (α y : ℝ) : ℝ :=
  (cosineTauberianProfile 0 - cosineTauberianProfile y) * y ^ (-1 - α)

theorem integrableOn_cosineTauberianMellinWeight
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    IntegrableOn (cosineTauberianMellinWeight α) (Ioi 0) := by
  let w : ℝ → ℝ := cosineTauberianMellinWeight α
  have hwmeas : Measurable w := by
    change Measurable fun y : ℝ => (1 - Real.cos y) * y ^ (-1 - α)
    fun_prop
  have hsmallPow : IntegrableOn (fun y : ℝ => y ^ (1 - α)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsmallMajorant : IntegrableOn
      (fun y : ℝ => (1 / 2 : ℝ) * y ^ (1 - α)) (Ioc 0 1) :=
    hsmallPow.const_mul _
  have hsmall : IntegrableOn w (Ioc 0 1) := by
    apply hsmallMajorant.integrable.mono' hwmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hypos : 0 < y := hy.1
    have hcos0 : 0 ≤ 1 - Real.cos y := sub_nonneg.mpr (Real.cos_le_one y)
    have hcos2 : 1 - Real.cos y ≤ y ^ 2 / 2 := by
      have h := Real.one_sub_sq_div_two_le_cos (x := y)
      linarith
    have hrpow : 0 ≤ y ^ (-1 - α) := Real.rpow_nonneg hypos.le _
    have hmul : y ^ 2 * y ^ (-1 - α) = y ^ (1 - α) := by
      rw [← Real.rpow_natCast y 2, ← Real.rpow_add hypos]
      congr 1
      ring
    dsimp [w, cosineTauberianMellinWeight]
    rw [abs_of_nonneg (mul_nonneg hcos0 hrpow)]
    calc
      (1 - Real.cos y) * y ^ (-1 - α) ≤
          (y ^ 2 / 2) * y ^ (-1 - α) :=
        mul_le_mul_of_nonneg_right hcos2 hrpow
      _ = (1 / 2 : ℝ) * y ^ (1 - α) := by
        calc
          y ^ 2 * 2⁻¹ * y ^ (-1 - α) = (1 / 2 : ℝ) * (y ^ 2 * y ^ (-1 - α)) := by ring
          _ = (1 / 2 : ℝ) * y ^ (1 - α) := by rw [hmul]
  have htailPow : IntegrableOn (fun y : ℝ => y ^ (-1 - α)) (Ioi 1) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have htailMajorant : IntegrableOn
      (fun y : ℝ => 2 * y ^ (-1 - α)) (Ioi 1) := htailPow.const_mul _
  have htail : IntegrableOn w (Ioi 1) := by
    apply htailMajorant.integrable.mono' hwmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := lt_trans zero_lt_one hy
    have hrpow : 0 ≤ y ^ (-1 - α) := Real.rpow_nonneg hypos.le _
    have hcos : 1 - Real.cos y ≤ 2 := by
      have h := Real.neg_one_le_cos y
      linarith
    have hcos0 : 0 ≤ 1 - Real.cos y := sub_nonneg.mpr (Real.cos_le_one y)
    dsimp [w, cosineTauberianMellinWeight]
    rw [abs_of_nonneg (mul_nonneg hcos0 hrpow)]
    exact mul_le_mul_of_nonneg_right hcos hrpow
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨hsmall, htail⟩

theorem integral_cosineTauberianMellinWeight_scale
    {α s : ℝ} (hs : 0 < s) :
    (∫ y in Ioi (0 : ℝ), (1 - Real.cos (s * y)) * y ^ (-1 - α)) =
      s ^ α * ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α y := by
  have hchange := integral_comp_mul_right_Ioi
    (fun y : ℝ => cosineTauberianMellinWeight α y) 0 hs
  have hpoint : ∀ y ∈ Ioi (0 : ℝ),
      (1 - Real.cos (s * y)) * y ^ (-1 - α) =
        s ^ (1 + α) * cosineTauberianMellinWeight α (s * y) := by
    intro y hy
    have hypos : 0 < y := hy
    have hmul : (s * y) ^ (-1 - α) = s ^ (-1 - α) * y ^ (-1 - α) :=
      Real.mul_rpow hs.le hy.le
    have hexp : s ^ (1 + α) * s ^ (-1 - α) = 1 := by
      rw [← Real.rpow_add hs]
      norm_num
    dsimp [cosineTauberianMellinWeight]
    calc
      (1 - Real.cos (s * y)) * y ^ (-1 - α) =
          (s ^ (1 + α) * s ^ (-1 - α)) *
            ((1 - Real.cos (s * y)) * y ^ (-1 - α)) := by rw [hexp]; ring
      _ = s ^ (1 + α) *
          ((1 - Real.cos (s * y)) * (s * y) ^ (-1 - α)) := by
        rw [hmul]
        ring
      _ = s ^ (1 + α) * cosineTauberianMellinWeight α (s * y) := by rfl
  have hcongr :
      (fun y : ℝ => (1 - Real.cos (s * y)) * y ^ (-1 - α)) =ᵐ[volume.restrict (Ioi 0)]
        (fun y => s ^ (1 + α) * cosineTauberianMellinWeight α (s * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hpoint y hy
  calc
    (∫ y in Ioi (0 : ℝ), (1 - Real.cos (s * y)) * y ^ (-1 - α)) =
        s ^ (1 + α) *
          ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α (s * y) := by
      rw [integral_congr_ae hcongr, integral_const_mul]
    _ = s ^ (1 + α) *
        (s⁻¹ * ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α y) := by
      rw [show (∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α (s * y)) =
          s⁻¹ * ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α y from by
        simpa [smul_eq_mul, mul_comm s] using
          (integral_comp_mul_right_Ioi
            (cosineTauberianMellinWeight α) 0 hs)]
    _ = s ^ α * ∫ y in Ioi (0 : ℝ), cosineTauberianMellinWeight α y := by
      rw [show 1 + α = α + 1 by ring, Real.rpow_add hs α 1]
      simp [Real.rpow_one, mul_assoc, hs.ne']

theorem integrableOn_scaledCosineTauberianMellinWeight
    {α s : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) (hs : 0 < s) :
    IntegrableOn (fun y : ℝ => (1 - Real.cos (s * y)) * y ^ (-1 - α)) (Ioi 0) := by
  let w : ℝ → ℝ := cosineTauberianMellinWeight α
  have hw : IntegrableOn w (Ioi 0) := integrableOn_cosineTauberianMellinWeight hα₀ hα₂
  have hw' : IntegrableOn w (Ioi (s * 0)) := by simpa using hw
  have hcomp : IntegrableOn (fun y : ℝ => w (s * y)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff w 0 hs).2 hw'
  have hpoint : ∀ y ∈ Ioi (0 : ℝ),
      (1 - Real.cos (s * y)) * y ^ (-1 - α) =
        s ^ (1 + α) * w (s * y) := by
    intro y hy
    have hypos : 0 < y := hy
    have hmul : (s * y) ^ (-1 - α) = s ^ (-1 - α) * y ^ (-1 - α) :=
      Real.mul_rpow hs.le hy.le
    have hexp : s ^ (1 + α) * s ^ (-1 - α) = 1 := by
      rw [← Real.rpow_add hs]
      norm_num
    dsimp [w, cosineTauberianMellinWeight]
    calc
      (1 - Real.cos (s * y)) * y ^ (-1 - α) =
          (s ^ (1 + α) * s ^ (-1 - α)) *
            ((1 - Real.cos (s * y)) * y ^ (-1 - α)) := by rw [hexp]; ring
      _ = s ^ (1 + α) *
          ((1 - Real.cos (s * y)) * (s * y) ^ (-1 - α)) := by rw [hmul]; ring
  have hmulInt : IntegrableOn
      (fun y : ℝ => s ^ (1 + α) * w (s * y)) (Ioi 0) := by
    exact hcomp.const_mul (s ^ (1 + α))
  exact hmulInt.congr_fun (fun y hy => (hpoint y hy).symm) measurableSet_Ioi

private noncomputable def mellinIntegrand (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  cosineTauberianKernel p.1 *
    ((1 - Real.cos (p.1 * p.2)) * p.2 ^ (-1 - α))

private theorem integrable_mellinIntegrand
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    Integrable (mellinIntegrand α)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × ℝ → ℝ := mellinIntegrand α
  have hFmeas : AEStronglyMeasurable F (μ.prod μ) := by
    have hcont : ContinuousOn (mellinIntegrand α) (Ioi (0 : ℝ) ×ˢ Ioi 0) := by
      change ContinuousOn (fun p : ℝ × ℝ =>
        cosineTauberianKernel p.1 *
          ((1 - Real.cos (p.1 * p.2)) * p.2 ^ (-1 - α))) _
      have hK : ContinuousOn
          (fun p : ℝ × ℝ => cosineTauberianKernel p.1)
          (Ioi (0 : ℝ) ×ˢ Ioi 0) :=
        (continuous_cosineTauberianKernel.comp continuous_fst).continuousOn
      have hrest : ContinuousOn
          (fun p : ℝ × ℝ => (1 - Real.cos (p.1 * p.2)) * p.2 ^ (-1 - α))
          (Ioi (0 : ℝ) ×ˢ Ioi 0) := by
        have hcos : Continuous fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2) := by
          fun_prop
        have hpow : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (-1 - α))
            (Ioi (0 : ℝ) ×ˢ Ioi 0) := by
          intro p hp
          have hy : p.2 ≠ 0 := ne_of_gt hp.2
          have hAt : ContinuousAt (fun y : ℝ => y ^ (-1 - α)) p.2 :=
            Real.continuousAt_rpow_const p.2 _ (Or.inl hy)
          exact (hAt.comp continuousAt_snd).continuousWithinAt
        exact hcos.continuousOn.mul hpow
      exact hK.mul hrest
    change AEStronglyMeasurable (mellinIntegrand α)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  rw [integrable_prod_iff hFmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := hs
    have hweight := integrableOn_scaledCosineTauberianMellinWeight hα₀ hα₂ hspos
    have hprod : Integrable (fun y : ℝ =>
        cosineTauberianKernel s * ((1 - Real.cos (s * y)) * y ^ (-1 - α))) μ := by
      simpa [μ, mellinIntegrand] using
        hweight.const_mul (cosineTauberianKernel s)
    exact hprod
  · let J : ℝ := cosineTauberianCosineMoment α
    let major : ℝ → ℝ := fun s => J * (s ^ α * |cosineTauberianKernel s|)
    have hMellinAbs := integrableOn_rpow_mul_abs_cosineTauberianKernel hα₀ hα₂
    have hmajorOn : IntegrableOn major (Ioi 0) := by
      have hm : IntegrableOn
          (fun s : ℝ => J * (s ^ α * |cosineTauberianKernel s|)) (Ioi 0) :=
        hMellinAbs.const_mul J
      exact hm.congr_fun (fun _ _ => by dsimp [major]) measurableSet_Ioi
    have hmajor : Integrable major μ := by
      simpa [μ, IntegrableOn] using hmajorOn
    have hinnerEq :
        (fun s : ℝ => ∫ y, ‖F (s, y)‖ ∂μ) =ᵐ[μ] major := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hspos : 0 < s := hs
      have hnorm :
          (fun y : ℝ => ‖F (s, y)‖) =ᵐ[μ]
            (fun y => |cosineTauberianKernel s| *
              ((1 - Real.cos (s * y)) * y ^ (-1 - α))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hypos : 0 < y := hy
        have hcos0 : 0 ≤ 1 - Real.cos (s * y) :=
          sub_nonneg.mpr (Real.cos_le_one _)
        have hrpow : 0 ≤ y ^ (-1 - α) := Real.rpow_nonneg hypos.le _
        have hg : 0 ≤ (1 - Real.cos (s * y)) * y ^ (-1 - α) :=
          mul_nonneg hcos0 hrpow
        change ‖cosineTauberianKernel s *
          ((1 - Real.cos (s * y)) * y ^ (-1 - α))‖ = _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
      calc
        (∫ y, ‖F (s, y)‖ ∂μ) =
            |cosineTauberianKernel s| *
              ∫ y, (1 - Real.cos (s * y)) * y ^ (-1 - α) ∂μ := by
          rw [integral_congr_ae hnorm, integral_const_mul]
        _ = |cosineTauberianKernel s| *
            (s ^ α * J) := by
          simp only [μ, cosineTauberianCosineMoment, J]
          rw [integral_cosineTauberianMellinWeight_scale hspos]
        _ = major s := by
          dsimp [major, J]
          ring
    exact hmajor.congr hinnerEq.symm

theorem cosineTauberianMellinMoment_mul_cosineMoment_eq_profileGapMoment
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    cosineTauberianCosineMoment α * cosineTauberianMellinMoment α =
      (Real.pi / 2) *
        ∫ y in Ioi (0 : ℝ), cosineTauberianProfileGapWeight α y := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × ℝ → ℝ := mellinIntegrand α
  have hF := integrable_mellinIntegrand hα₀ hα₂
  have huncurry : Function.uncurry (fun s y : ℝ =>
      cosineTauberianKernel s * ((1 - Real.cos (s * y)) * y ^ (-1 - α))) =
      mellinIntegrand α := by
    funext p
    rfl
  have hswap := integral_integral_swap
    (f := fun s y : ℝ =>
      cosineTauberianKernel s * ((1 - Real.cos (s * y)) * y ^ (-1 - α))) (by
      rw [huncurry]
      exact hF)
  have hleftEq :
      (fun s : ℝ => ∫ y, F (s, y) ∂μ) =ᵐ[μ]
        (fun s => cosineTauberianCosineMoment α *
          (s ^ α * cosineTauberianKernel s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := hs
    calc
      (∫ y, F (s, y) ∂μ) =
          cosineTauberianKernel s *
            ∫ y, (1 - Real.cos (s * y)) * y ^ (-1 - α) ∂μ := by
        rw [show (fun y : ℝ => F (s, y)) =
            fun y => cosineTauberianKernel s *
              ((1 - Real.cos (s * y)) * y ^ (-1 - α)) from by
                funext y
                rfl,
          integral_const_mul]
      _ = cosineTauberianKernel s *
          (s ^ α * cosineTauberianCosineMoment α) := by
        simp only [μ, cosineTauberianCosineMoment]
        rw [integral_cosineTauberianMellinWeight_scale hspos]
      _ = cosineTauberianCosineMoment α *
          (s ^ α * cosineTauberianKernel s) := by ring
  have hleft :
      (∫ s, ∫ y, F (s, y) ∂μ ∂μ) =
        cosineTauberianCosineMoment α * cosineTauberianMellinMoment α := by
    calc
      (∫ s, ∫ y, F (s, y) ∂μ ∂μ) =
          ∫ s, cosineTauberianCosineMoment α *
            (s ^ α * cosineTauberianKernel s) ∂μ := integral_congr_ae hleftEq
      _ = cosineTauberianCosineMoment α *
          ∫ s, s ^ α * cosineTauberianKernel s ∂μ := integral_const_mul _ _
      _ = cosineTauberianCosineMoment α * cosineTauberianMellinMoment α := by
        simp [μ, cosineTauberianMellinMoment]
  have hrightEq :
      (fun y : ℝ => ∫ s, F (s, y) ∂μ) =ᵐ[μ]
        (fun y => (Real.pi / 2) * cosineTauberianProfileGapWeight α y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hy
    calc
      (∫ s, F (s, y) ∂μ) =
          (∫ s, (1 - Real.cos (s * y)) * cosineTauberianKernel s ∂μ) *
            y ^ (-1 - α) := by
        rw [show (fun s : ℝ => F (s, y)) =
            fun s => ((1 - Real.cos (s * y)) * cosineTauberianKernel s) *
              y ^ (-1 - α) from by
                funext s
                dsimp [F, mellinIntegrand]
                ring,
          integral_mul_const]
      _ = (Real.pi / 2) *
          (cosineTauberianProfile 0 - cosineTauberianProfile y) *
            y ^ (-1 - α) := by
        rw [integral_Ioi_one_sub_cos_mul_cosineTauberianKernel]
      _ = (Real.pi / 2) * cosineTauberianProfileGapWeight α y := by
        simp only [cosineTauberianProfileGapWeight]
        ring
  calc
    cosineTauberianCosineMoment α * cosineTauberianMellinMoment α =
        ∫ s, ∫ y, F (s, y) ∂μ ∂μ := hleft.symm
    _ = ∫ y, ∫ s, F (s, y) ∂μ ∂μ := hswap
    _ = ∫ y, (Real.pi / 2) *
          cosineTauberianProfileGapWeight α y ∂μ := integral_congr_ae hrightEq
    _ = (Real.pi / 2) *
          ∫ y in Ioi (0 : ℝ), cosineTauberianProfileGapWeight α y := by
        simp [μ, integral_const_mul]

private theorem profileGapWeight_eq_small
    {α y : ℝ} (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    cosineTauberianProfileGapWeight α y =
      (1 / 2 : ℝ) * y ^ (1 - α) - (1 / 3 : ℝ) * y ^ (2 - α) := by
  have hcap := cosineTauberianProfile_gap_eq_cappedCubic
    (x := 1) (y := y) (by norm_num : (0 : ℝ) < 1)
  have habs : |y| = y := abs_of_nonneg hy₀.le
  have hgap : cosineTauberianProfile 0 - cosineTauberianProfile y =
      y ^ 2 / 2 - y ^ 3 / 3 := by
    simpa [habs, min_eq_left hy₁] using hcap
  have hpow₂ : y ^ 2 * y ^ (-1 - α) = y ^ (1 - α) := by
    rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy₀]
    congr 1
    ring
  have hpow₃ : y ^ 3 * y ^ (-1 - α) = y ^ (2 - α) := by
    rw [← Real.rpow_natCast y 3, ← Real.rpow_add hy₀]
    congr 1
    ring
  rw [cosineTauberianProfileGapWeight, hgap, div_eq_mul_inv, div_eq_mul_inv]
  calc
    (y ^ 2 * 2⁻¹ - y ^ 3 * 3⁻¹) * y ^ (-1 - α) =
        (1 / 2 : ℝ) * (y ^ 2 * y ^ (-1 - α)) -
          (1 / 3 : ℝ) * (y ^ 3 * y ^ (-1 - α)) := by ring
    _ = (1 / 2 : ℝ) * y ^ (1 - α) -
          (1 / 3 : ℝ) * y ^ (2 - α) := by rw [hpow₂, hpow₃]

private theorem profileGapWeight_eq_tail
    {α y : ℝ} (hy : 1 < y) :
    cosineTauberianProfileGapWeight α y =
      (1 / 6 : ℝ) * y ^ (-1 - α) := by
  have hypos : 0 < y := lt_trans zero_lt_one hy
  have hlarge : 1 ≤ |y| := by rw [abs_of_pos hypos]; exact le_of_lt hy
  have hprofile : cosineTauberianProfile y = 0 := by
    rw [cosineTauberianProfile, max_eq_right (sub_nonpos.mpr hlarge)]
    norm_num
  have hzero : cosineTauberianProfile 0 = 1 / 6 := by
    norm_num [cosineTauberianProfile]
  simp [cosineTauberianProfileGapWeight, hprofile, hzero]

theorem integrableOn_cosineTauberianProfileGapWeight
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    IntegrableOn (cosineTauberianProfileGapWeight α) (Ioi 0) := by
  let g : ℝ → ℝ := cosineTauberianProfileGapWeight α
  have hgmeas : Measurable g := by
    change Measurable fun y : ℝ =>
      (cosineTauberianProfile 0 - cosineTauberianProfile y) * y ^ (-1 - α)
    have hprofile : Measurable cosineTauberianProfile :=
      continuous_cosineTauberianProfile.measurable
    have hrpow : Measurable fun y : ℝ => y ^ (-1 - α) := by fun_prop
    exact (measurable_const.sub hprofile).mul hrpow
  have hsmallPow₁ : IntegrableOn (fun y : ℝ => y ^ (1 - α)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsmallPow₂ : IntegrableOn (fun y : ℝ => y ^ (2 - α)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsmallMajorant : IntegrableOn
      (fun y : ℝ => (1 / 2 : ℝ) * y ^ (1 - α) -
        (1 / 3 : ℝ) * y ^ (2 - α)) (Ioc 0 1) :=
    (hsmallPow₁.const_mul _).sub (hsmallPow₂.const_mul _)
  have hsmall : IntegrableOn g (Ioc 0 1) := by
    apply hsmallMajorant.congr_fun
      (fun y hy => (profileGapWeight_eq_small hy.1 hy.2).symm) measurableSet_Ioc
  have htailPow : IntegrableOn (fun y : ℝ => y ^ (-1 - α)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have htailMajorant : IntegrableOn
      (fun y : ℝ => (1 / 6 : ℝ) * y ^ (-1 - α)) (Ioi 1) :=
    htailPow.const_mul _
  have htail : IntegrableOn g (Ioi 1) := by
    apply htailMajorant.congr_fun
      (fun y hy => (profileGapWeight_eq_tail hy).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨hsmall, htail⟩

theorem integral_cosineTauberianProfileGapWeight
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    (∫ y in Ioi (0 : ℝ), cosineTauberianProfileGapWeight α y) =
      1 / (α * (2 - α) * (3 - α)) := by
  let g : ℝ → ℝ := cosineTauberianProfileGapWeight α
  have hgSmall : IntegrableOn g (Ioc 0 1) := by
    exact (integrableOn_cosineTauberianProfileGapWeight hα₀ hα₂).mono_set
      (by intro y hy; exact hy.1)
  have hgTail : IntegrableOn g (Ioi 1) := by
    exact (integrableOn_cosineTauberianProfileGapWeight hα₀ hα₂).mono_set
      (by intro y hy; exact lt_trans zero_lt_one hy)
  have hsmall :
      (∫ y in Ioc (0 : ℝ) 1, g y) =
        1 / (2 * (2 - α)) - 1 / (3 * (3 - α)) := by
    have hEq : EqOn g
        (fun y : ℝ => (1 / 2 : ℝ) * y ^ (1 - α) -
          (1 / 3 : ℝ) * y ^ (2 - α)) (Ioc 0 1) := by
      intro y hy
      exact profileGapWeight_eq_small hy.1 hy.2
    rw [integral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall hEq))]
    rw [← intervalIntegral.integral_of_le (μ := volume)
      (f := fun y : ℝ => (1 / 2 : ℝ) * y ^ (1 - α) -
        (1 / 3 : ℝ) * y ^ (2 - α)) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_sub
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < 1 - α)),
      integral_rpow (Or.inl (by linarith : -1 < 2 - α))]
    have h₁ : 0 < 1 - α + 1 := by linarith
    have h₂ : 0 < 2 - α + 1 := by linarith
    simp [Real.zero_rpow, ne_of_gt h₁, ne_of_gt h₂]
    have h₂α : 0 < 2 - α := by linarith
    have h₃α : 0 < 3 - α := by linarith
    field_simp [ne_of_gt h₂α, ne_of_gt h₃α]
    ring_nf
  have htail :
      (∫ y in Ioi (1 : ℝ), g y) = 1 / (6 * α) := by
    have hEq : EqOn g (fun y : ℝ => (1 / 6 : ℝ) * y ^ (-1 - α)) (Ioi 1) := by
      intro y hy
      exact profileGapWeight_eq_tail hy
    rw [integral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall hEq)), integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    simp only [Real.one_rpow]
    rw [show -1 - α + 1 = -α by ring]
    field_simp [ne_of_gt hα₀]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hgSmall hgTail,
    hsmall, htail]
  have h2 : 0 < 2 - α := by linarith
  have h3 : 0 < 3 - α := by linarith
  field_simp [ne_of_gt hα₀, ne_of_gt h2, ne_of_gt h3]
  ring

theorem cosineTauberianCosineMoment_pos
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    0 < cosineTauberianCosineMoment α := by
  let f : ℝ → ℝ := cosineTauberianMellinWeight α
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hf_int : Integrable f μ := by
    simpa [f, μ, IntegrableOn] using
      (integrableOn_cosineTauberianMellinWeight hα₀ hα₂)
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hy
    dsimp [f, cosineTauberianMellinWeight]
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one y))
      (Real.rpow_nonneg hypos.le _)
  have hinterval : Ioo (Real.pi / 2) Real.pi ⊆ Function.support f := by
    intro y hy
    have hypos : 0 < y := (by positivity : 0 < Real.pi / 2).trans hy.1
    have hcos : Real.cos y ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_lt hy.1)
        (le_trans (le_of_lt hy.2)
          (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)))
    have hweight : 0 < y ^ (-1 - α) := Real.rpow_pos_of_pos hypos _
    change f y ≠ 0
    dsimp [f, cosineTauberianMellinWeight]
    exact ne_of_gt (mul_pos (by linarith) hweight)
  have hinterval_subset_domain : Ioo (Real.pi / 2) Real.pi ⊆ Ioi 0 := by
    intro y hy
    exact (by positivity : (0 : ℝ) < Real.pi / 2).trans hy.1
  have hinterval_measure :
      0 < μ (Ioo (Real.pi / 2) Real.pi) := by
    have hrestrict : μ (Ioo (Real.pi / 2) Real.pi) =
        volume (Ioo (Real.pi / 2) Real.pi) := by
      dsimp [μ]
      rw [Measure.restrict_apply measurableSet_Ioo]
      rw [inter_eq_left.mpr hinterval_subset_domain]
    rw [hrestrict]
    rw [Real.volume_Ioo]
    have hπ2 : 0 < Real.pi / 2 := by positivity
    have hlength : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    rw [hlength]
    exact ENNReal.ofReal_pos.mpr hπ2
  have hsupport_measure : 0 < μ (Function.support f) :=
    lt_of_lt_of_le hinterval_measure (measure_mono hinterval)
  rw [show cosineTauberianCosineMoment α = ∫ y, f y ∂μ by
    rfl]
  exact (integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int).2 hsupport_measure

theorem cosineTauberianMellinMoment_pos
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    0 < cosineTauberianMellinMoment α := by
  have hJ : 0 < cosineTauberianCosineMoment α :=
    cosineTauberianCosineMoment_pos hα₀ hα₂
  have hgap : 0 <
      (Real.pi / 2) *
        ∫ y in Ioi (0 : ℝ), cosineTauberianProfileGapWeight α y := by
    rw [integral_cosineTauberianProfileGapWeight hα₀ hα₂]
    have h₂ : 0 < 2 - α := by linarith
    have h₃ : 0 < 3 - α := by linarith
    exact mul_pos (by positivity)
      (one_div_pos.mpr (mul_pos (mul_pos hα₀ h₂) h₃))
  have hproduct : 0 <
      cosineTauberianCosineMoment α * cosineTauberianMellinMoment α := by
    rw [cosineTauberianMellinMoment_mul_cosineMoment_eq_profileGapMoment hα₀ hα₂]
    exact hgap
  have hquotient : 0 <
      (cosineTauberianCosineMoment α * cosineTauberianMellinMoment α) /
        cosineTauberianCosineMoment α := div_pos hproduct hJ
  have heq :
      (cosineTauberianCosineMoment α * cosineTauberianMellinMoment α) /
        cosineTauberianCosineMoment α = cosineTauberianMellinMoment α := by
    field_simp [ne_of_gt hJ]
  rwa [heq] at hquotient

noncomputable def cosineTauberianConstant (α : ℝ) : ℝ :=
  (2 / Real.pi) * cosineTauberianMellinMoment α

theorem cosineTauberianConstant_eq
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    cosineTauberianConstant α =
      1 / (α * (2 - α) * (3 - α) * cosineTauberianCosineMoment α) := by
  have hJ : 0 < cosineTauberianCosineMoment α :=
    cosineTauberianCosineMoment_pos hα₀ hα₂
  have h₂ : 0 < 2 - α := by linarith
  have h₃ : 0 < 3 - α := by linarith
  have hD : 0 < α * (2 - α) * (3 - α) :=
    mul_pos (mul_pos hα₀ h₂) h₃
  have hπ : 0 < Real.pi := Real.pi_pos
  have hidentity :=
    cosineTauberianMellinMoment_mul_cosineMoment_eq_profileGapMoment hα₀ hα₂
  rw [cosineTauberianConstant]
  rw [integral_cosineTauberianProfileGapWeight hα₀ hα₂] at hidentity
  calc
    (2 / Real.pi) * cosineTauberianMellinMoment α =
        ((cosineTauberianCosineMoment α * cosineTauberianMellinMoment α) *
          (2 / Real.pi)) / cosineTauberianCosineMoment α := by
      field_simp [ne_of_gt hπ, ne_of_gt hJ]
    _ = ((Real.pi / 2) *
          (1 / (α * (2 - α) * (3 - α))) * (2 / Real.pi)) /
          cosineTauberianCosineMoment α := by rw [hidentity]
    _ = 1 / (α * (2 - α) * (3 - α) * cosineTauberianCosineMoment α) := by
      field_simp [ne_of_gt hπ, ne_of_gt hD, ne_of_gt hJ]

theorem cosineTauberianConstant_pos
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    0 < cosineTauberianConstant α := by
  rw [cosineTauberianConstant_eq hα₀ hα₂]
  have h₂ : 0 < 2 - α := by linarith
  have h₃ : 0 < 3 - α := by linarith
  exact one_div_pos.mpr
    (mul_pos (mul_pos (mul_pos hα₀ h₂) h₃)
      (cosineTauberianCosineMoment_pos hα₀ hα₂))

end Analysis.Fourier.CosineTauberian

end
