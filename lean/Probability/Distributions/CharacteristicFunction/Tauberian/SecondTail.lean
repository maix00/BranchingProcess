/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.Moments.Truncated.TailIntegral
public import Probability.Distributions.CharacteristicFunction.Tauberian.Kernel.Fourier
public import Probability.Distributions.CharacteristicFunction.Symmetrization
public import Probability.Distributions.CharacteristicFunction.CosineDefect
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Twice-integrated tails and cosine defects

This module connects two-sided tails to the cosine defect of their measure.
For an increment law's squared-modulus characteristic defect, the relevant
measure is its symmetrization.
-/

open MeasureTheory Set
open scoped Interval FourierTransform RealInnerProductSpace Complex

@[expose] public section

namespace ProbabilityTheory

private theorem intervalIntegral_min_abs_sq {x y : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) =
      x * (min |y| x) ^ 2 - (2 / 3 : ℝ) * (min |y| x) ^ 3 := by
  let a : ℝ := min |y| x
  have ha0 : 0 ≤ a := le_min (abs_nonneg y) hx
  have hax : a ≤ x := min_le_right _ _
  have hEq : EqOn (fun t : ℝ => (min |y| t) ^ 2)
      (fun t => (min a t) ^ 2) (uIcc 0 x) := by
    intro t ht
    change (min |y| t) ^ 2 = (min a t) ^ 2
    have ht' : t ∈ Icc (0 : ℝ) x := by
      simpa [uIcc_of_le hx] using ht
    by_cases hyx : |y| ≤ x
    · have ha : a = |y| := by simp [a, min_eq_left hyx]
      rw [ha]
    · have hxy : x < |y| := lt_of_not_ge hyx
      have ha : a = x := by simp [a, min_eq_right (le_of_lt hxy)]
      have hminY : min |y| t = t := min_eq_right (le_trans ht'.2 (le_of_lt hxy))
      rw [hminY, ha, min_eq_right ht'.2]
  have hleftEq : EqOn (fun t : ℝ => (min a t) ^ 2)
      (fun t => t ^ 2) (uIcc 0 a) := by
    intro t ht
    change (min a t) ^ 2 = t ^ 2
    have ht' : t ∈ Icc (0 : ℝ) a := by
      simpa [uIcc_of_le ha0] using ht
    rw [min_eq_right ht'.2]
  have hrightEq : EqOn (fun t : ℝ => (min a t) ^ 2)
      (fun _ => a ^ 2) (uIcc a x) := by
    intro t ht
    change (min a t) ^ 2 = a ^ 2
    have ht' : t ∈ Icc a x := by
      simpa [uIcc_of_le hax] using ht
    rw [min_eq_left ht'.1]
  have hint (l r : ℝ) : IntervalIntegrable
      (fun t : ℝ => (min a t) ^ 2) volume l r :=
    (by fun_prop : Continuous fun t : ℝ => (min a t) ^ 2).intervalIntegrable l r
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
      (hint 0 a) (hint a x)).symm
  have hleft : (∫ t in (0 : ℝ)..a, (min a t) ^ 2) = a ^ 3 / 3 := by
    rw [intervalIntegral.integral_congr hleftEq, integral_pow]
    norm_num
  have hright : (∫ t in a..x, (min a t) ^ 2) = (x - a) * a ^ 2 := by
    rw [intervalIntegral.integral_congr hrightEq, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  calc
    (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) =
        ∫ t in (0 : ℝ)..x, (min a t) ^ 2 := intervalIntegral.integral_congr hEq
    _ = (∫ t in (0 : ℝ)..a, (min a t) ^ 2) +
        ∫ t in a..x, (min a t) ^ 2 := hsplit
    _ = x * a ^ 2 - (2 / 3 : ℝ) * a ^ 3 := by rw [hleft, hright]; ring
    _ = x * (min |y| x) ^ 2 - (2 / 3 : ℝ) * (min |y| x) ^ 3 := by rfl

/-- The second tail integral is the expectation of an explicit capped cubic
function. This is the layer-cake identity needed to match the Fourier
profile; it uses only a probability measure, not a density. -/
theorem secondTailIntegral_twoSidedTail_eq_cappedCubic
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Asymptotics.secondTailIntegral
        (fun t => μ.real {y : ℝ | t < |y|}) x =
      ∫ y, (x * (min |y| x) ^ 2 / 2 -
        (min |y| x) ^ 3 / 3) ∂μ := by
  let f : ℝ → ℝ → ℝ := fun t y =>
    (min |y| (min (max t 0) x)) ^ 2
  letI : IsFiniteMeasure (volume.restrict (uIoc 0 x)) := by
    rw [uIoc_of_le hx]
    infer_instance
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc 0 x)).prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry f)
        ((volume.restrict (uIoc 0 x)).prod μ) := by
      exact (by fun_prop : Measurable (Function.uncurry f)).aestronglyMeasurable
    have hbound : ∀ᵐ z ∂((volume.restrict (uIoc 0 x)).prod μ),
        ‖Function.uncurry f z‖ ≤ x ^ 2 := by
      filter_upwards [] with z
      have hcap0 : 0 ≤ min (max z.1 0) x := le_min (le_max_right _ _) hx
      have hcaple : min (max z.1 0) x ≤ x := min_le_right _ _
      have hmin0 : 0 ≤ min |z.2| (min (max z.1 0) x) :=
        le_min (abs_nonneg _) hcap0
      have hminle : min |z.2| (min (max z.1 0) x) ≤ x :=
        (min_le_right _ _).trans hcaple
      dsimp [f, Function.uncurry]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ hmin0 hx).2 hminle
    exact Integrable.of_bound hmeas (x ^ 2) hbound
  have hswap := intervalIntegral_integral_swap
      (a := (0 : ℝ)) (b := x) (f := f) hprod
  have hinner (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) x) :
      truncatedSquareTailIntegral μ t =
        ∫ y, (min |y| t) ^ 2 ∂μ := by
    have ht' : t ∈ Icc (0 : ℝ) x := by
      simpa [uIcc_of_le hx] using ht
    simpa [truncatedSquareTailIntegral] using
      (integral_sq_min_abs_eq_layercake_tail μ ht'.1).symm
  have htail :=
    secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral
      μ hx
  have houter :
      (∫ t in (0 : ℝ)..x, truncatedSquareTailIntegral μ t) =
        ∫ t in (0 : ℝ)..x, ∫ y, (min |y| t) ^ 2 ∂μ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hinner t ht
  have hleft :
      (∫ t in (0 : ℝ)..x, ∫ y, f t y ∂μ) =
        ∫ t in (0 : ℝ)..x, ∫ y, (min |y| t) ^ 2 ∂μ := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by
      simpa [uIcc_of_le hx] using ht
    have hpoint (y : ℝ) : f t y = (min |y| t) ^ 2 := by
      dsimp [f]
      rw [max_eq_left ht'.1, min_eq_left ht'.2]
    apply integral_congr_ae
    filter_upwards [] with y
    exact hpoint y
  have hright : ∀ y : ℝ,
      (∫ t in (0 : ℝ)..x, f t y) =
        ∫ t in (0 : ℝ)..x, (min |y| t) ^ 2 := by
    intro y
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by
      simpa [uIcc_of_le hx] using ht
    dsimp [f]
    rw [max_eq_left ht'.1, min_eq_left ht'.2]
  have hsecond :
      Asymptotics.secondTailIntegral
          (fun t => μ.real {y : ℝ | t < |y|}) x =
        (1 / 2 : ℝ) *
          (∫ y, (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) ∂μ) := by
    calc
      _ = (1 / 2 : ℝ) *
          (∫ t in (0 : ℝ)..x, truncatedSquareTailIntegral μ t) := htail
      _ = (1 / 2 : ℝ) *
          (∫ t in (0 : ℝ)..x, ∫ y, (min |y| t) ^ 2 ∂μ) := by rw [houter]
      _ = (1 / 2 : ℝ) *
          (∫ t in (0 : ℝ)..x, ∫ y, f t y ∂μ) := by rw [← hleft]
      _ = (1 / 2 : ℝ) *
          (∫ y, (∫ t in (0 : ℝ)..x, f t y) ∂μ) := by
            exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) hswap
      _ = (1 / 2 : ℝ) *
          (∫ y, (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) ∂μ) := by
            have hrightInt :
                (∫ y, (∫ t in (0 : ℝ)..x, f t y) ∂μ) =
                  ∫ y, (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact hright y
            exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) hrightInt
  rw [hsecond]
  calc
    (1 / 2 : ℝ) * (∫ y, (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) ∂μ) =
        ∫ y, (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..x, (min |y| t) ^ 2) ∂μ := by
          rw [integral_const_mul]
    _ = ∫ y, (x * (min |y| x) ^ 2 / 2 -
          (min |y| x) ^ 3 / 3) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [intervalIntegral_min_abs_sq hx]
          ring

/-- Exact scaled inverse-cosine identity for the twice-integrated two-sided
tail. Fubini is justified by the integrability of the Tauberian kernel and
the uniform bound `0 ≤ 1 - cos ≤ 2`; no moment assumption is used. -/
theorem secondTailIntegral_eq_cosineDefect_kernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 < x) :
    Asymptotics.secondTailIntegral
        (fun t => μ.real {y : ℝ | t < |y|}) x =
      (2 / Real.pi) * x ^ 3 *
        (∫ s in Ioi (0 : ℝ),
          cosineDefectIntegral μ (s / x) * cosineTauberianKernel s) := by
  let f : ℝ × ℝ → ℝ := fun p =>
    (1 - Real.cos ((p.1 / x) * p.2)) * cosineTauberianKernel p.1
  have hKabs : Integrable (fun s : ℝ => |cosineTauberianKernel s|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [Real.norm_eq_abs] using
      (integrableOn_cosineTauberianKernel.norm)
  have hbase : Integrable
      (fun s : ℝ => 2 * |cosineTauberianKernel s|)
      (volume.restrict (Ioi (0 : ℝ))) := hKabs.const_mul 2
  have hbaseProd : Integrable
      (fun p : ℝ × ℝ => 2 * |cosineTauberianKernel p.1|)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := hbase.comp_fst μ
  have hfmeas : AEStronglyMeasurable f
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
    exact ((by fun_prop [cosineTauberianKernel] : Measurable f)
      |>.aestronglyMeasurable)
  have hbound : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod μ),
      ‖f p‖ ≤ 2 * |cosineTauberianKernel p.1| := by
    filter_upwards [] with p
    have hlow : -1 ≤ Real.cos ((p.1 / x) * p.2) :=
      Real.neg_one_le_cos _
    have hupp : Real.cos ((p.1 / x) * p.2) ≤ 1 := Real.cos_le_one _
    have hdefect0 : 0 ≤ 1 - Real.cos ((p.1 / x) * p.2) := by linarith
    have hdefect2 : 1 - Real.cos ((p.1 / x) * p.2) ≤ 2 := by linarith
    dsimp [f]
    rw [abs_mul, abs_of_nonneg hdefect0]
    exact mul_le_mul_of_nonneg_right hdefect2 (abs_nonneg _)
  have hf : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
    hbaseProd.mono' hfmeas hbound
  have hpoint (s : ℝ) :
      cosineDefectIntegral μ (s / x) * cosineTauberianKernel s =
        ∫ y, f (s, y) ∂μ := by
    have hdefect : Integrable (fun y : ℝ =>
        1 - Real.cos ((s / x) * y)) μ := by
      apply Integrable.of_bound (by fun_prop) 2
      filter_upwards [] with y
      have hlow := Real.neg_one_le_cos ((s / x) * y)
      have hupp := Real.cos_le_one ((s / x) * y)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith :
        0 ≤ 1 - Real.cos ((s / x) * y))]
      linarith
    calc
      _ = cosineTauberianKernel s * cosineDefectIntegral μ (s / x) := by ring
      _ = cosineTauberianKernel s *
          (∫ y, 1 - Real.cos ((s / x) * y) ∂μ) := by
            rw [cosineDefectIntegral]
      _ = ∫ y, cosineTauberianKernel s *
          (1 - Real.cos ((s / x) * y)) ∂μ := by
            rw [← integral_const_mul]
      _ = ∫ y, f (s, y) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with y
            dsimp [f]
            ring
  have houter :
      (∫ s in Ioi (0 : ℝ),
        cosineDefectIntegral μ (s / x) * cosineTauberianKernel s) =
        ∫ s in Ioi (0 : ℝ), ∫ y, f (s, y) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact hpoint s
  have hdouble :
      (∫ s in Ioi (0 : ℝ), ∫ y, f (s, y) ∂μ) =
        ∫ y, ∫ s in Ioi (0 : ℝ), f (s, y) ∂volume ∂μ := by
    calc
      _ = ∫ p, f p ∂((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
        (integral_prod f hf).symm
      _ = ∫ y, ∫ s, f (s, y) ∂(volume.restrict (Ioi (0 : ℝ))) ∂μ :=
        integral_prod_symm f hf
      _ = ∫ y, ∫ s in Ioi (0 : ℝ), f (s, y) ∂volume ∂μ := rfl
  have hkernel (y : ℝ) :
      (∫ s in Ioi (0 : ℝ), f (s, y) ∂volume) =
        (Real.pi / 2) *
          (cosineTauberianProfile 0 - cosineTauberianProfile (y / x)) := by
    have harg (s : ℝ) : (s / x) * y = s * (y / x) := by
      field_simp [ne_of_gt hx]
    calc
      (∫ s in Ioi (0 : ℝ), f (s, y) ∂volume) =
          ∫ s in Ioi (0 : ℝ),
            (1 - Real.cos (s * (y / x))) * cosineTauberianKernel s ∂volume := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro s hs
              simp only [f]
              rw [harg]
      _ = (Real.pi / 2) *
          (cosineTauberianProfile 0 - cosineTauberianProfile (y / x)) :=
            integral_Ioi_one_sub_cos_mul_cosineTauberianKernel (y / x)
  have hgap : Integrable
      (fun y : ℝ => cosineTauberianProfile 0 -
        cosineTauberianProfile (y / x)) μ := by
    have hbounded : ∀ᵐ y ∂μ,
        ‖cosineTauberianProfile 0 - cosineTauberianProfile (y / x)‖ ≤ 1 := by
      filter_upwards [] with y
      have hprofileNonneg (z : ℝ) : 0 ≤ cosineTauberianProfile z := by
        dsimp [cosineTauberianProfile]
        positivity
      have hprofileLe (z : ℝ) : cosineTauberianProfile z ≤ 1 / 6 := by
        by_cases hz : 1 - |z| ≤ 0
        · rw [cosineTauberianProfile, max_eq_right hz]
          norm_num
        · have hz0 : 0 ≤ 1 - |z| := le_of_not_ge hz
          have hz1 : 1 - |z| ≤ 1 := by nlinarith [abs_nonneg z]
          have hfactor : 1 + 2 * |z| = 3 - 2 * (1 - |z|) := by ring
          rw [cosineTauberianProfile, max_eq_left hz0, hfactor]
          have hpoly : 1 - (1 - |z|) ^ 2 * (3 - 2 * (1 - |z|)) =
              (1 - (1 - |z|)) ^ 2 * (1 + 2 * (1 - |z|)) := by ring
          have hnonneg : 0 ≤ (1 - (1 - |z|)) ^ 2 *
              (1 + 2 * (1 - |z|)) :=
            mul_nonneg (sq_nonneg _) (by positivity)
          nlinarith
      have hzero : cosineTauberianProfile 0 = 1 / 6 := by
        norm_num [cosineTauberianProfile]
      have hval := hprofileNonneg (y / x)
      have hvalLe := hprofileLe (y / x)
      rw [Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> nlinarith
    have hm : AEStronglyMeasurable
        (fun y : ℝ => cosineTauberianProfile 0 -
          cosineTauberianProfile (y / x)) μ := by
      exact ((by fun_prop [cosineTauberianProfile] : Measurable fun y : ℝ =>
        cosineTauberianProfile 0 - cosineTauberianProfile (y / x))
          |>.aestronglyMeasurable)
    exact Integrable.of_bound hm 1 hbounded
  have hdouble' :
      (∫ s in Ioi (0 : ℝ),
        cosineDefectIntegral μ (s / x) * cosineTauberianKernel s) =
        (Real.pi / 2) *
          (∫ y, cosineTauberianProfile 0 -
            cosineTauberianProfile (y / x) ∂μ) := by
    calc
      _ = ∫ y, ∫ s in Ioi (0 : ℝ), f (s, y) ∂volume ∂μ :=
        houter.trans hdouble
      _ = ∫ y, (Real.pi / 2) *
            (cosineTauberianProfile 0 - cosineTauberianProfile (y / x)) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact hkernel y
      _ = (Real.pi / 2) *
          (∫ y, cosineTauberianProfile 0 -
            cosineTauberianProfile (y / x) ∂μ) := by rw [integral_const_mul]
  have hcap := secondTailIntegral_twoSidedTail_eq_cappedCubic μ hx.le
  have hcapProfile :
      (∫ y, (x * (min |y| x) ^ 2 / 2 -
          (min |y| x) ^ 3 / 3) ∂μ) =
        x ^ 3 * (∫ y, cosineTauberianProfile 0 -
          cosineTauberianProfile (y / x) ∂μ) := by
    calc
      _ = ∫ y, x ^ 3 * (cosineTauberianProfile 0 -
            cosineTauberianProfile (y / x)) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact (cosineTauberianProfile_gap_eq_cappedCubic hx).symm
      _ = x ^ 3 * (∫ y, cosineTauberianProfile 0 -
            cosineTauberianProfile (y / x) ∂μ) := by rw [integral_const_mul]
  calc
    _ = x ^ 3 *
        (∫ y, cosineTauberianProfile 0 -
          cosineTauberianProfile (y / x) ∂μ) := hcap.trans hcapProfile
    _ = x ^ 3 * ((2 / Real.pi) *
        (∫ s in Ioi (0 : ℝ),
          cosineDefectIntegral μ (s / x) * cosineTauberianKernel s)) := by
            rw [hdouble']
            field_simp [Real.pi_ne_zero]
    _ = (2 / Real.pi) * x ^ 3 *
        (∫ s in Ioi (0 : ℝ),
          cosineDefectIntegral μ (s / x) * cosineTauberianKernel s) := by ring


end ProbabilityTheory

end
