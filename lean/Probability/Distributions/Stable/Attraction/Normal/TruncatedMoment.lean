/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.CharacteristicFunction.TruncatedMoment
public import Probability.Distributions.CharacteristicFunction.FirstOrder
public import Probability.Distributions.Moments.Truncated.TailIntegral
public import Probability.Distributions.Stable.Attraction.Normal.CharacteristicTail
public import Probability.Distributions.Stable.Attraction.Norming.Centering
public import Probability.Distributions.DomainOfAttraction.Centering
public import Analysis.Asymptotics.RegularVariation.AtZero.Potter
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Truncated moments in the normal domain of attraction

Gaussian attraction implies Feller's quadratic-tail condition and hence slow
variation of the truncated second moment. This includes infinite-variance
normal domains of attraction.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private theorem one_sub_norm_charFun_sq_eq_two_cosineDefect_sub_norm_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    1 - ‖charFun ν t‖ ^ 2 =
      2 * cosineDefectIntegral ν t - ‖charFun ν t - 1‖ ^ 2 := by
  rw [cosineDefectIntegral_eq_one_sub_charFun_re]
  let z : ℂ := charFun ν t
  have h₁ : ‖z - 1‖ ^ 2 - (z.re - 1) ^ 2 = z.im ^ 2 := by
    simpa [z] using Complex.sq_norm_sub_sq_re (z - 1)
  have h₂ : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 :=
    Complex.sq_norm_sub_sq_im z
  nlinarith [h₁, h₂]

private theorem normDefect_le_truncatedSecondMoment_add_closedTail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {x : ℝ} (hx : 0 < x) :
    1 - ‖charFun ν x⁻¹‖ ^ 2 ≤
      truncatedSecondMoment ν x / x ^ 2 +
        4 * ν.real {y : ℝ | x ≤ |y|} := by
  have hcosUpper := cosineDefectIntegral_upper_bound_truncatedSecondMoment_add_tail ν hx
  have hdefect : 1 - ‖charFun ν x⁻¹‖ ^ 2 ≤
      2 * cosineDefectIntegral ν x⁻¹ := by
    rw [cosineDefectIntegral_eq_one_sub_charFun_re]
    have hnorm := norm_charFun_le_one (μ := ν) (x⁻¹)
    have hre := Complex.re_le_norm (charFun ν x⁻¹)
    nlinarith
  have htailSub : {y : ℝ | x < |y|} ⊆ {y : ℝ | x ≤ |y|} := by
    intro y hy
    change x < |y| at hy
    exact le_of_lt hy
  have htail := measureReal_mono (μ := ν) htailSub (measure_ne_top ν _)
  calc
    1 - ‖charFun ν x⁻¹‖ ^ 2 ≤ 2 * cosineDefectIntegral ν x⁻¹ := hdefect
    _ ≤ 2 * (truncatedSecondMoment ν x / (2 * x ^ 2) +
          2 * ν.real {y : ℝ | x < |y|}) :=
      mul_le_mul_of_nonneg_left hcosUpper (by norm_num)
    _ = truncatedSecondMoment ν x / x ^ 2 +
          4 * ν.real {y : ℝ | x < |y|} := by field_simp [hx.ne']; ring
    _ ≤ truncatedSecondMoment ν x / x ^ 2 +
          4 * ν.real {y : ℝ | x ≤ |y|} :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail (by norm_num))

/-- Gaussian attraction forces the Feller quadratic-tail condition, without a
finite variance assumption. The argument compares the cosine defect with the
truncated second moment and the closed tail, then uses the characteristic-tail
estimate. -/
private theorem gaussian_truncatedSecondMoment_data
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    (Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) ∧
      (∀ᶠ x : ℝ in atTop, 0 < truncatedSecondMoment ν x) := by
  let D : ℝ → ℝ := fun x => 1 - ‖charFun ν (x⁻¹)‖ ^ 2
  let T : ℝ → ℝ := fun x => ν.real {y : ℝ | x ≤ |y|}
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have htail := h.tendsto_closedAbsTail_div_normDefect_atTop_of_gaussian
  have hDpos : ∀ᶠ x : ℝ in atTop, 0 < D x := by
    let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
      (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
    have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
    exact tendsto_inv_atTop_nhdsGT_zero.eventually hpos
  have hsmall : ∀ᶠ x : ℝ in atTop, 4 * T x / D x ≤ 1 / 2 := by
    have h := htail.const_mul (4 : ℝ)
    have h' : Tendsto (fun x : ℝ => 4 * T x / D x) atTop (nhds 0) := by
      have hEq : (fun x : ℝ => 4 * (T x / D x)) =ᶠ[atTop]
          fun x => 4 * T x / D x := by
        filter_upwards [] with x
        ring
      simpa using h.congr' hEq
    filter_upwards [h'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    exact le_of_lt hx
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hDpos, hsmall] with x hx hDx hs
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hineq := normDefect_le_truncatedSecondMoment_add_closedTail ν hx
    have hDt : D x ≤ V x / x ^ 2 + 4 * T x := by
      simpa [D, T, V] using hineq
    have htailSmall : 4 * T x ≤ D x / 2 := by
      have hs' := (div_le_iff₀ hDx).mp hs
      nlinarith
    have hVlower : D x / 2 ≤ V x / x ^ 2 := by linarith
    have hVratio : 0 < V x / x ^ 2 := lt_of_lt_of_le (div_pos hDx (by norm_num)) hVlower
    exact (div_pos_iff_of_pos_right hx2).mp hVratio
  have hbound : ∀ᶠ x : ℝ in atTop,
      0 ≤ x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ∧
        x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ≤ 2 * (T x / D x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hDpos, hVpos, hsmall]
      with x hx hDx hVx hs
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hineq := normDefect_le_truncatedSecondMoment_add_closedTail ν hx
    have hDt : D x ≤ V x / x ^ 2 + 4 * T x := by
      simpa [D, T, V] using hineq
    have hsmall' : 4 * T x ≤ D x / 2 := by
      have hs' := (div_le_iff₀ hDx).mp hs
      nlinarith
    have hVratio : D x / 2 ≤ V x / x ^ 2 := by linarith
    have hVmul : x ^ 2 * D x ≤ 2 * V x := by
      have := (le_div_iff₀ hx2).mp hVratio
      nlinarith
    have htailOpen : 0 ≤ ν.real {y : ℝ | x < |y|} := measureReal_nonneg
    have htailClosed : 0 ≤ T x := measureReal_nonneg
    have htailLe : ν.real {y : ℝ | x < |y|} ≤ T x := by
      have hle := measureReal_mono (μ := ν)
        (s₁ := {y : ℝ | x < |y|}) (s₂ := {y : ℝ | x ≤ |y|})
        (by intro y hy; exact le_of_lt (by change x < |y| at hy; exact hy))
        (measure_ne_top ν _)
      simpa [T] using hle
    have hcross : x ^ 2 * ν.real {y : ℝ | x < |y|} * D x ≤
        2 * T x * V x := by
      calc
        x ^ 2 * ν.real {y : ℝ | x < |y|} * D x ≤ x ^ 2 * T x * D x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htailLe (sq_nonneg x)) hDx.le
        _ = T x * (x ^ 2 * D x) := by ring
        _ ≤ T x * (2 * V x) := by nlinarith [mul_le_mul_of_nonneg_left hVmul htailClosed]
        _ = 2 * T x * V x := by ring
    have hdiv : x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ≤ 2 * (T x / D x) := by
      rw [div_le_iff₀ hVx, div_eq_mul_inv]
      calc
        x ^ 2 * ν.real {y : ℝ | x < |y|} ≤
            (2 * T x * V x) / D x := (le_div_iff₀ hDx).2 (by simpa [mul_assoc] using hcross)
        _ = 2 * (T x / D x) * V x := by field_simp
    exact ⟨div_nonneg (mul_nonneg (sq_nonneg x) htailOpen) hVx.le, hdiv⟩
  have hupper := htail.const_mul (2 : ℝ)
  have hupper' : Tendsto (fun x : ℝ => 2 * (T x / D x)) atTop (nhds 0) := by
    simpa [T, D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hupper
  have hlimit := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper'
    (hbound.mono fun x hx => hx.1)
    (hbound.mono fun x hx => hx.2)
  exact ⟨by simpa [V] using hlimit, hVpos⟩

/-- Gaussian attraction forces Feller's quadratic-tail condition, without a
finite variance assumption. -/
theorem IsInDomainOfAttractionAlong.tendsto_secondTailRatio_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0) :=
  (gaussian_truncatedSecondMoment_data h).1

/-- The truncated second moment is eventually positive in the normal domain
of attraction, including the infinite-variance case. -/
theorem IsInDomainOfAttractionAlong.eventually_pos_truncatedSecondMoment_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    ∀ᶠ x : ℝ in atTop, 0 < truncatedSecondMoment ν x :=
  (gaussian_truncatedSecondMoment_data h).2

/-- The truncated second moment is slowly varying throughout the normal
domain of attraction, including the infinite-variance case. -/
theorem IsInDomainOfAttractionAlong.truncatedSecondMoment_isSlowlyVarying_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν) := by
  apply isSlowlyVarying_truncatedSecondMoment_of_tendsto_secondTailRatio ν
  · exact h.eventually_pos_truncatedSecondMoment_of_gaussian
  · exact h.tendsto_secondTailRatio_of_gaussian

/-- The Mogulskii factor `L*` at the normal endpoint is slowly varying for
every Gaussian domain of attraction, even when the increment law has infinite
variance. -/
theorem IsInDomainOfAttractionAlong.stableSlowVariation_two_isSlowlyVarying_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν) := by
  rw [show stableSlowVariation 2 ν = truncatedSecondMoment ν by
    funext x
    exact stableSlowVariation_two ν x]
  exact h.truncatedSecondMoment_isSlowlyVarying_of_gaussian

/-- Feller's condition and Potter's bound make the integrated tail beyond a
large cutoff negligible compared with `V(x) / x`. The exponent `1/2` in
Potter's envelope is chosen only to make the resulting power integrable. -/
private theorem tendsto_tailIntegral_div_truncatedSecondMoment_mul_radius_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (habsolute : Integrable (fun x : ℝ => |x|) ν)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν))
    (hFeller : Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) :
    Tendsto (fun x : ℝ => x *
      (∫ t in Ioi x, ν.real {y : ℝ | t < |y|}) /
        truncatedSecondMoment ν x) atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let p : ℝ := 1 / 2
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V 0 := by
    simpa [V] using hVslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    refine ⟨0, ?_⟩
    intro x y hx hxy
    exact truncatedSecondMoment_mono ν hx hxy
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : 0 < p)
  obtain ⟨Rpositive, hRpositive⟩ := eventually_atTop.1 hVslow.1
  have htailIntegrable : IntegrableOn tail (Ioi (0 : ℝ)) volume := by
    simpa [tail] using integrableOn_twoSidedTail_of_integrable_abs ν habsolute
      (by norm_num : (0 : ℝ) ≤ 0)
  have htailAntitone : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := ν)
    · intro y hy
      exact lt_of_le_of_lt hab hy
  have htailMeasurable : Measurable tail := htailAntitone.measurable
  have hfactor : (2 : ℝ) ^ p ≤ 2 := by
    have hp : p ≤ 1 := by dsimp [p]; norm_num
    simpa [p, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp)
  have hFellerEventually (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ x : ℝ in atTop,
        x ^ 2 * tail x / V x ≤ ε := by
    filter_upwards [hFeller.eventually (Iio_mem_nhds hε)] with x hx
    exact le_of_lt (by simpa [tail, V] using hx)
  have hIntegralBound (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ x : ℝ in atTop,
        (∫ t in Ioi x, tail t) ≤ 4 * ε * V x / x := by
    obtain ⟨RFeller, hRFeller⟩ := eventually_atTop.1 (hFellerEventually ε hε)
    let R : ℝ := max 1 (max Rpotter (max Rpositive RFeller))
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRpotterLe : Rpotter ≤ R := by
      dsimp [R]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hRpositiveLe : Rpositive ≤ R := by
      dsimp [R]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hRFellerLe : RFeller ≤ R := by
      dsimp [R]
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hVpos : ∀ ⦃x : ℝ⦄, R ≤ x → 0 < V x := by
      intro x hx
      exact hRpositive x (le_trans hRpositiveLe hx)
    have hFellerSmall : ∀ ⦃x : ℝ⦄, R ≤ x → x ^ 2 * tail x / V x ≤ ε := by
      intro x hx
      exact hRFeller x (le_trans hRFellerLe hx)
    have hPotter : ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y →
        V y / V x ≤ 2 ^ p * (y / x) ^ p := by
      intro x y hx hxy
      simpa [p] using hpotter (le_trans hRpotterLe hx) hxy
    have hbound (x t : ℝ) (hx : R ≤ x) (ht : x < t) :
        tail t ≤ (2 * ε * V x / x ^ p) * t ^ (p - 2) := by
      have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
      have htpos : 0 < t := lt_trans hxpos ht
      have hxSq : 0 < x ^ 2 := sq_pos_of_pos hxpos
      have htSq : 0 < t ^ 2 := sq_pos_of_pos htpos
      have hVx : 0 < V x := hVpos hx
      have hVt : 0 < V t := hVpos (le_trans hx ht.le)
      have hratio := hPotter hx ht.le
      have hratioNonneg : 0 ≤ (t / x) ^ p :=
        Real.rpow_nonneg (div_nonneg htpos.le hxpos.le) p
      have hratioBound : V t ≤ 2 * V x * (t / x) ^ p := by
        have hratio' : V t ≤ V x * (2 ^ p * (t / x) ^ p) := by
          simpa [mul_comm] using (div_le_iff₀ hVx).mp hratio
        calc
          V t ≤ V x * (2 ^ p * (t / x) ^ p) := hratio'
          _ ≤ V x * (2 * (t / x) ^ p) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hfactor hratioNonneg) hVx.le
          _ = 2 * V x * (t / x) ^ p := by ring
      have hF := hFellerSmall (le_trans hx ht.le)
      have hF' : t ^ 2 * tail t ≤ ε * V t :=
        (div_le_iff₀ hVt).mp hF
      have htail' : tail t ≤ ε * V t / t ^ 2 :=
        (le_div_iff₀ htSq).2 (by simpa [mul_comm] using hF')
      have htail'' : tail t ≤ ε * (2 * V x * (t / x) ^ p) / t ^ 2 :=
        htail'.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratioBound hε.le) htSq.le)
      have hdivPow : (t / x) ^ p = t ^ p / x ^ p :=
        Real.div_rpow htpos.le hxpos.le p
      have hpowSub : t ^ p / t ^ (2 : ℕ) = t ^ (p - 2) := by
        rw [← Real.rpow_natCast t 2]
        exact (Real.rpow_sub htpos p 2).symm
      have hxpow : 0 < x ^ p := Real.rpow_pos_of_pos hxpos p
      have hteq : ε * (2 * V x * (t / x) ^ p) / t ^ 2 =
          (2 * ε * V x / x ^ p) * t ^ (p - 2) := by
        calc
          _ = (2 * ε * V x / x ^ p) * (t ^ p / t ^ 2) := by
            rw [hdivPow]
            field_simp [ne_of_gt hxpow, ne_of_gt htSq]
          _ = _ := by rw [hpowSub]
      exact htail''.trans_eq hteq
    filter_upwards [eventually_ge_atTop R] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
    have hVx : 0 < V x := hVpos hx
    have hC : 0 ≤ 2 * ε * V x / x ^ p :=
      div_nonneg (by positivity) (Real.rpow_pos_of_pos hxpos p).le
    have htailX : IntegrableOn tail (Ioi x) volume :=
      htailIntegrable.mono_set (Ioi_subset_Ioi hxpos.le)
    have hpowInt : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Ioi x) volume :=
      integrableOn_Ioi_rpow_of_lt (by dsimp [p]; norm_num) hxpos
    have hmajorInt : IntegrableOn
        (fun t : ℝ => (2 * ε * V x / x ^ p) * t ^ (p - 2)) (Ioi x) volume :=
      hpowInt.const_mul _
    have hmonoIntegral := setIntegral_mono_on htailX hmajorInt measurableSet_Ioi
      (fun t ht => hbound x t hx ht)
    calc
      (∫ t in Ioi x, tail t) ≤
          ∫ t in Ioi x, (2 * ε * V x / x ^ p) * t ^ (p - 2) := hmonoIntegral
      _ = (2 * ε * V x / x ^ p) *
          (∫ t in Ioi x, t ^ (p - 2)) := by rw [integral_const_mul]
      _ = (2 * ε * V x / x ^ p) *
          (-x ^ (p - 2 + 1) / (p - 2 + 1)) := by
        rw [integral_Ioi_rpow_of_lt (by dsimp [p]; norm_num) hxpos]
      _ = 4 * ε * V x / x := by
        have hp : p = 1 / 2 := rfl
        subst p
        have hpow : x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
          rw [← Real.rpow_add hxpos]
          rw [show (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 by ring,
            Real.rpow_neg_one]
        have hcoef : -x ^ (-(1 / 2 : ℝ)) / (-(1 / 2 : ℝ)) =
            2 * x ^ (-(1 / 2 : ℝ)) := by
          field_simp
        rw [show (1 / 2 : ℝ) - 2 + 1 = -(1 / 2 : ℝ) by ring, hcoef]
        rw [div_eq_mul_inv]
        calc
          (2 * ε * V x * (x ^ (1 / 2 : ℝ))⁻¹) *
              (2 * x ^ (-(1 / 2 : ℝ))) =
              4 * ε * V x * ((x ^ (1 / 2 : ℝ))⁻¹ *
                (x ^ (1 / 2 : ℝ))⁻¹) := by
            rw [Real.rpow_neg hxpos.le]
            ring
          _ = 4 * ε * V x *
              (x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))) := by
                rw [← Real.rpow_neg hxpos.le]
          _ = 4 * ε * V x * x⁻¹ := by rw [hpow]
          _ = 4 * ε * V x / x := by rw [div_eq_mul_inv]
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := hVslow.1
  have hVpositive : ∀ᶠ x : ℝ in atTop, V x ≠ 0 := hVpos.mono fun x hx => hx.ne'
  have htailNonneg : ∀ x, 0 ≤ ∫ t in Ioi x, tail t := by
    intro x
    exact setIntegral_nonneg measurableSet_Ioi fun t _ => measureReal_nonneg
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos] with x hx hVx
    have hnonneg : 0 ≤ x * (∫ t in Ioi x, tail t) / V x :=
      div_nonneg (mul_nonneg hx.le (htailNonneg x)) hVx.le
    linarith
  · intro ε hε
    let η : ℝ := ε / 8
    have hη : 0 < η := by dsimp [η]; linarith
    have hFsmall : ∀ᶠ x : ℝ in atTop,
        x ^ 2 * tail x / V x < ε / 2 :=
      hFeller.eventually (Iio_mem_nhds (by linarith))
    have hIbound := hIntegralBound η hη
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos, hFsmall, hIbound]
      with x hx hVx hFx hIx
    have hterm : x * (∫ t in Ioi x, tail t) / V x ≤ 4 * η := by
      apply (div_le_iff₀ hVx).2
      calc
        x * (∫ t in Ioi x, tail t) ≤
            x * (4 * η * V x / x) :=
          mul_le_mul_of_nonneg_left hIx hx.le
        _ = 4 * η * V x := by field_simp [hx.ne']
    have hdecomp :
        x * (∫ t in Ioi x, tail t) / V x ≤ ε / 2 := by
      dsimp [η] at hterm
      linarith
    exact hdecomp.trans_lt (by linarith)

/-- In the Gaussian domain of attraction, the discarded absolute first moment
is negligible relative to the cutoff and its truncated second moment. This
combines Feller's quadratic-tail condition with the integrated-tail estimate
above and the layer-cake identity. -/
theorem tendsto_radius_mul_discardedAbsFirstMoment_div_truncatedSecondMoment_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (habsolute : Integrable (fun x : ℝ => |x|) ν)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν))
    (hFeller : Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) :
    Tendsto (fun x : ℝ => x *
      (∫ y, {z : ℝ | x < |z|}.indicator (fun z => |z|) y ∂ν) /
        truncatedSecondMoment ν x) atTop (nhds 0) := by
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let tailIntegral : ℝ → ℝ := fun x => ∫ t in Ioi x, tail t
  have hintegral := tendsto_tailIntegral_div_truncatedSecondMoment_mul_radius_zero
    habsolute hVslow hFeller
  have hsum : Tendsto (fun x : ℝ =>
      x ^ 2 * tail x / truncatedSecondMoment ν x +
        x * tailIntegral x / truncatedSecondMoment ν x)
      atTop (nhds (0 + 0)) := by
    simpa [tail, tailIntegral] using hFeller.add hintegral
  have heq : (fun x : ℝ => x *
      (∫ y, {z : ℝ | x < |z|}.indicator (fun z => |z|) y ∂ν) /
        truncatedSecondMoment ν x) =ᶠ[atTop]
      fun x => x ^ 2 * tail x / truncatedSecondMoment ν x +
        x * tailIntegral x / truncatedSecondMoment ν x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVslow.1] with x hx hVx
    have hlayer := integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral
      ν habsolute hx.le
    dsimp [tail, tailIntegral]
    rw [hlayer]
    field_simp [ne_of_gt hVx]
  simpa using hsum.congr' heq.symm

/-- Every law in the normal domain of attraction has a finite first absolute
moment. Gaussian attraction gives Feller's tail condition; slow variation of
the truncated second moment and Potter's bound then make the integrated tail
finite. -/
theorem IsInDomainOfAttractionAlong.integrable_id_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Integrable (id : ℝ → ℝ) ν := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  have hslow := h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V 0 := by
    simpa [V] using hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    refine ⟨0, ?_⟩
    intro x y hx hxy
    exact truncatedSecondMoment_mono ν hx hxy
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Rpos, hRpos⟩ := eventually_atTop.1 hslow.eventually_pos
  let Rbase : ℝ := max Rpotter (max Rpos 1)
  have hRbasePos : 0 < Rbase := by dsimp [Rbase]; positivity
  have hRbasePotter : Rpotter ≤ Rbase := by
    dsimp [Rbase]
    exact le_max_left _ _
  have hRbaseMoment : Rpos ≤ Rbase := by
    dsimp [Rbase]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hVbase : 0 < V Rbase := hRpos Rbase hRbaseMoment
  let p : ℝ := 1 / 2
  let C : ℝ := V Rbase * 2 ^ p / Rbase ^ p
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hVbound : ∀ᶠ x : ℝ in atTop, V x ≤ C * x ^ p := by
    filter_upwards [eventually_ge_atTop Rbase] with x hx
    have hp := hpotter hRbasePotter hx
    have hratio : V x / V Rbase ≤ 2 ^ p * (x / Rbase) ^ p := by
      simpa [V, p, Real.rpow_zero] using hp
    have hmul : V x ≤ V Rbase * (2 ^ p * (x / Rbase) ^ p) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hVbase).mp hratio
    have hdivpow : (x / Rbase) ^ p = x ^ p / Rbase ^ p :=
      Real.div_rpow (le_of_lt (lt_of_lt_of_le hRbasePos hx)) hRbasePos.le p
    have hpowPos : 0 < Rbase ^ p := Real.rpow_pos_of_pos hRbasePos p
    have heq : V Rbase * (2 ^ p * (x ^ p / Rbase ^ p)) = C * x ^ p := by
      dsimp [C]
      field_simp [hpowPos.ne']
    rw [hdivpow] at hmul
    rw [heq] at hmul
    exact hmul
  have htailRatio := h.tendsto_secondTailRatio_of_gaussian
  have htailSmall : ∀ᶠ x : ℝ in atTop, x ^ 2 * tail x / V x ≤ 1 := by
    have h := htailRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h] with x hx
    exact le_of_lt (by simpa [tail, V] using hx)
  have htailAntitone : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := ν)
    · intro y hy
      exact lt_of_le_of_lt hab hy
  have htailMeas : Measurable tail := htailAntitone.measurable
  obtain ⟨Rsmall, hRsmall⟩ := eventually_atTop.1 htailSmall
  obtain ⟨Rbound, hRbound⟩ := eventually_atTop.1 hVbound
  let R : ℝ := max Rbase (max Rsmall (max Rbound 1))
  have hRbaseLe : Rbase ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hRsmallLe : Rsmall ≤ R := by
    dsimp [R]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRboundLe : Rbound ≤ R := by
    dsimp [R]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have htailBound : ∀ x, R ≤ x → tail x ≤ C * x ^ (p - 2) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
    have hVx : 0 < V x := lt_of_lt_of_le hVbase
      (truncatedSecondMoment_mono ν hRbasePos.le (le_trans hRbaseLe hx))
    have hratio := hRsmall x (le_trans hRsmallLe hx)
    have hVupper := hRbound x (le_trans hRboundLe hx)
    have htailV : x ^ 2 * tail x ≤ V x := by
      have := (div_le_iff₀ hVx).mp hratio
      nlinarith [mul_nonneg (sq_nonneg x) (measureReal_nonneg : 0 ≤ tail x)]
    have htailToV : tail x ≤ V x / x ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hxpos)).2 (by simpa [mul_comm] using htailV)
    have hVToPower : V x / x ^ 2 ≤ C * x ^ (p - 2) := by
      calc
        V x / x ^ 2 ≤ (C * x ^ p) / x ^ 2 :=
          div_le_div_of_nonneg_right hVupper (sq_nonneg x)
        _ = C * x ^ (p - 2) := by
          rw [← Real.rpow_natCast x 2]
          rw [Real.rpow_sub hxpos p 2]
          field_simp [pow_ne_zero 2 hxpos.ne']
          ring_nf
    exact htailToV.trans hVToPower
  have hmajorant : IntegrableOn (fun x : ℝ => C * x ^ (p - 2)) (Ioi R) volume := by
    have hpow : p - 2 < -1 := by dsimp [p]; norm_num
    exact (integrableOn_Ioi_rpow_of_lt hpow hRpos).const_mul C
  have htailIntegrable : IntegrableOn tail (Ioi R) volume := by
    apply hmajorant.mono' htailMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans hRpos hx
    have hbound := htailBound x hx.le
    have htailNonneg : 0 ≤ tail x := by dsimp [tail]; exact measureReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg htailNonneg] using hbound
  have htailLocal : IntegrableOn tail (Ioc 0 R) volume := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top htailMeas.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg : 0 ≤ tail x)]
    have hmass : tail x ≤ 1 := by
      dsimp [tail]
      calc
        ν.real {y : ℝ | x < |y|} ≤ ν.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := by simp
    exact hmass
  have htailZero : IntegrableOn tail (Ioi 0) volume := by
    have hset : Ioi R ∪ Ioc 0 R = Ioi 0 := by
      ext x
      simp only [mem_union, mem_Ioi, mem_Ioc]
      constructor
      · rintro (hx | ⟨hx, _⟩)
        · exact lt_trans hRpos hx
        · exact hx
      · intro hx
        by_cases hRx : R < x
        · exact Or.inl hRx
        · exact Or.inr ⟨hx, le_of_not_gt hRx⟩
    rw [← hset]
    exact htailIntegrable.union htailLocal
  simpa [tail] using integrable_id_of_integrableOn_twoSidedTail ν htailZero

/-- A Gaussian-domain normalization is sublinear, even without a finite
variance assumption. The Gaussian characteristic defect is regularly varying
at zero with index two and satisfies `n D(1/bₙ) → 1`. A Potter lower bound
gives `D(1/bₙ) ≤ C bₙ^(-3/2)`, which forces `bₙ / n → 0`. -/
theorem IsInDomainOfAttractionAlong.tendsto_scale_div_nat_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto (fun n : ℕ => scale n / (n : ℝ)) atTop (nhds 0) := by
  let D : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hdata := h.gaussian_defect_data
  have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
  have huniform := h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  have hpotter := Asymptotics.IsRegularlyVaryingAtZero.exists_potter_bound_of_uniform_ratio
    hpos huniform (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 2)
  obtain ⟨U, hUpos, hDpos, hbounds⟩ := hpotter
  let v : ℝ := U / 2
  have hvpos : 0 < v := by dsimp [v]; linarith
  have hvU : v < U := by dsimp [v]; linarith
  have hDv : 0 < D v := hDpos hvpos hvU
  let lower : ℝ := 1 / (2 * 2 ^ (2 - 1 / 2 : ℝ))
  have hlower : 0 < lower := by
    dsimp [lower]
    positivity
  let p : ℝ := 2 - 1 / 2
  let coeff : ℝ := lower * v ^ p
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    exact mul_pos hlower (Real.rpow_pos_of_pos hvpos p)
  let K : ℝ := D v / coeff
  have hK : 0 < K := div_pos hDv hcoeff
  have hscaleTop : Tendsto scale atTop atTop := hdata.2.1
  have hclock : Tendsto (fun n : ℕ => (n : ℝ) * D ((scale n)⁻¹))
      atTop (nhds 1) := by
    simpa [D] using hdata.2.2
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have hscaleLarge : ∀ᶠ n : ℕ in atTop, 1 / v ≤ scale n :=
    hscaleTop.eventually (eventually_ge_atTop (1 / v))
  have hclockLower : ∀ᶠ n : ℕ in atTop,
      1 / 2 < (n : ℝ) * D ((scale n)⁻¹) :=
    hclock.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hDscalePos : ∀ᶠ n : ℕ in atTop, 0 < D ((scale n)⁻¹) := by
    filter_upwards [hscalePos, hscaleLarge] with n hsn hlarge
    have hu : 0 < (scale n)⁻¹ := inv_pos.mpr hsn
    have hvleDiv : 1 / scale n ≤ v := by
      apply (div_le_iff₀ hsn).2
      have hmul := (div_le_iff₀ hvpos).mp hlarge
      nlinarith [hmul]
    have hvle : (scale n)⁻¹ ≤ v := by simpa only [one_div] using hvleDiv
    have huU : (scale n)⁻¹ < U := by
      exact lt_of_le_of_lt hvle hvU
    simpa [D] using hDpos hu huU
  have hDscalePow : ∀ᶠ n : ℕ in atTop,
      D ((scale n)⁻¹) * (scale n) ^ p ≤ K := by
    filter_upwards [hscalePos, hscaleLarge, hDscalePos] with n hsn hlarge hDn
    have hu : 0 < (scale n)⁻¹ := inv_pos.mpr hsn
    have hvuDiv : 1 / scale n ≤ v := by
      apply (div_le_iff₀ hsn).2
      have hmul := (div_le_iff₀ hvpos).mp hlarge
      nlinarith [hmul]
    have hvu : (scale n)⁻¹ ≤ v := by simpa only [one_div] using hvuDiv
    have hpot := hbounds hu hvu hvU
    have hratio : lower * (v / (scale n)⁻¹) ^ p ≤ D v / D ((scale n)⁻¹) := by
      simpa [lower, p, D] using hpot.1
    have hinvEq : v / (scale n)⁻¹ = v * scale n := by
      rw [div_eq_mul_inv, inv_inv]
    have hmulPow : (v * scale n) ^ p = v ^ p * (scale n) ^ p :=
      Real.mul_rpow hvpos.le hsn.le
    have hratio' : lower * (v ^ p * (scale n) ^ p) ≤
        D v / D ((scale n)⁻¹) := by
      simpa [hinvEq, hmulPow] using hratio
    have hcross : coeff * (D ((scale n)⁻¹) * (scale n) ^ p) ≤ D v := by
      have := (le_div_iff₀ hDn).mp hratio'
      dsimp [coeff] at *
      nlinarith [this]
    exact (le_div_iff₀ hcoeff).2 (by simpa [K, mul_comm, mul_left_comm,
      mul_assoc] using hcross)
  have hscalePowPos : ∀ᶠ n : ℕ in atTop, 0 < (scale n) ^ p := by
    filter_upwards [hscalePos] with n hn
    exact Real.rpow_pos_of_pos hn p
  have hscalePowBound : ∀ᶠ n : ℕ in atTop,
      (scale n) ^ p ≤ 2 * K * (n : ℝ) := by
    filter_upwards [hclockLower, hDscalePow, hnatPos, hDscalePos,
      hscalePowPos] with n hclockN hDpow hn hDn hbp
    have hmul : (1 / 2) * (scale n) ^ p <
        ((n : ℝ) * D ((scale n)⁻¹)) * (scale n) ^ p :=
      mul_lt_mul_of_pos_right hclockN hbp
    have hupper : ((n : ℝ) * D ((scale n)⁻¹)) * (scale n) ^ p ≤
        (n : ℝ) * K := by
      calc
        _ = (n : ℝ) * (D ((scale n)⁻¹) * (scale n) ^ p) := by ring
        _ ≤ (n : ℝ) * K := mul_le_mul_of_nonneg_left hDpow hn.le
    have hcombined := hmul.trans_le hupper
    have hfinal : (scale n) ^ p < 2 * ((n : ℝ) * K) := by
      calc
        (scale n) ^ p = 2 * ((1 / 2 : ℝ) * (scale n) ^ p) := by ring
        _ < 2 * ((n : ℝ) * K) :=
          mul_lt_mul_of_pos_left hcombined (by norm_num)
    exact le_of_lt (by simpa [mul_comm, mul_left_comm, mul_assoc] using hfinal)
  have hsqrtInv : Tendsto (fun n : ℕ => (Real.sqrt (scale n))⁻¹)
      atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hscaleTop)
  have hupper : Tendsto (fun n : ℕ => 2 * K * (Real.sqrt (scale n))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsqrtInv)
  have hratioBound : ∀ᶠ n : ℕ in atTop,
      scale n / (n : ℝ) ≤ 2 * K * (Real.sqrt (scale n))⁻¹ := by
    filter_upwards [hscalePowBound, hscalePos, hnatPos] with n hbp hsn hn
    have hsqrtPos : 0 < Real.sqrt (scale n) := Real.sqrt_pos.2 hsn
    have hpowEq : (scale n) ^ p = scale n * Real.sqrt (scale n) := by
      dsimp [p]
      rw [show (2 : ℝ) - (1 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by ring,
        Real.rpow_add hsn, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hdivBound : scale n / (n : ℝ) ≤
        2 * K / Real.sqrt (scale n) := by
      apply (div_le_iff₀ hn).2
      have hstep : scale n ≤ (2 * K * (n : ℝ)) / Real.sqrt (scale n) := by
        apply (le_div_iff₀ hsqrtPos).2
        simpa [hpowEq, mul_assoc, mul_left_comm, mul_comm] using hbp
      have hstep' : scale n ≤ (2 * K / Real.sqrt (scale n)) * (n : ℝ) := by
        calc
          scale n ≤ (2 * K * (n : ℝ)) / Real.sqrt (scale n) := hstep
          _ = (2 * K / Real.sqrt (scale n)) * (n : ℝ) := by
            field_simp [hsqrtPos.ne']
      exact hstep'
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdivBound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [hscalePos, hnatPos] with n hsn hn
    exact div_nonneg hsn.le hn.le
  · exact hratioBound

/-- Uncentered Gaussian attraction forces zero mean. Its characteristic
defect first gives a sublinear normalization; Gaussian attraction also gives
the finite first moment, so the strong-law centering criterion applies. -/
theorem IsInDomainOfAttractionAlong.integral_eq_zero_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0)) :
    (∫ x : ℝ, x ∂ν) = 0 := by
  exact integral_eq_zero_of_uncenteredAttraction_of_sublinearNormalization
    h h.integrable_id_of_gaussian h.tendsto_scale_div_nat_of_gaussian

/-- In the normal domain of attraction, the real-part characteristic defect
and the truncated second moment have their standard quadratic asymptotic.
This is the part of the exponent-two comparison that does not involve the
phase of the characteristic function. -/
theorem IsInDomainOfAttractionAlong.tendsto_normalizedCosineDefect_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => 2 * x ^ 2 * cosineDefectIntegral ν x⁻¹ /
        truncatedSecondMoment ν x) atTop (nhds 1) := by
  exact tendsto_normalizedCosineDefect_of_slowVariation_and_tail ν
    h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
    h.tendsto_secondTailRatio_of_gaussian

/-- In the normal domain, centering and a finite first moment make the phase
of the characteristic function negligible compared with the quadratic
cosine defect. Thus the truncated second moment is asymptotic to the squared-
modulus defect with the usual exponent-two normalization. No second moment is
assumed. -/
theorem IsInDomainOfAttractionAlong.tendsto_truncatedSecondMoment_div_scaledNormDefect_of_gaussian_of_integrable_centered
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    Tendsto
      (fun x : ℝ => truncatedSecondMoment ν x /
        (x ^ 2 * (1 - ‖charFun ν (x⁻¹)‖ ^ 2))) atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let D : ℝ → ℝ := fun x => 1 - ‖charFun ν (x⁻¹)‖ ^ 2
  let Q : ℝ → ℝ := fun x => cosineDefectIntegral ν (x⁻¹)
  have hcos : Tendsto (fun x : ℝ => 2 * x ^ 2 * Q x / V x)
      atTop (nhds 1) := by
    simpa [Q, V] using h.tendsto_normalizedCosineDefect_of_gaussian
  have hphase := tendsto_mul_charFun_sub_one_of_integrable_id_of_integral_eq_zero
    hint hmean
  have hphaseNormSq : Tendsto
      (fun x : ℝ => ‖(x : ℂ) * (charFun ν (x⁻¹) - 1)‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (hphase.norm.pow 2)
  have hphaseSq : Tendsto
      (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2)
      atTop (nhds 0) := by
    apply hphaseNormSq.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    ring
  have hVpos := h.eventually_pos_truncatedSecondMoment_of_gaussian
  obtain ⟨R, hR⟩ := eventually_atTop.1 hVpos
  let R' : ℝ := max R 1
  have hR'pos : 0 < R' := by
    dsimp [R']
    positivity
  have hR'large : R ≤ R' := by
    dsimp [R']
    exact le_max_left _ _
  have hVbase : 0 < V R' := by
    exact hR R' hR'large
  have hVlower : ∀ᶠ x : ℝ in atTop, V R' ≤ V x := by
    filter_upwards [eventually_ge_atTop R'] with x hx
    exact truncatedSecondMoment_mono ν hR'pos.le hx
  have herror : Tendsto
      (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x)
      atTop (nhds 0) := by
    have hupper := hphaseSq.div_const (V R')
    have hupper' : Tendsto
        (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V R')
        atTop (nhds 0) := by
      simpa [hVbase.ne'] using hupper
    have hbounds : ∀ᶠ x : ℝ in atTop,
        0 ≤ x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x ∧
          x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x ≤
            x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V R' := by
      filter_upwards [hVlower, hVpos] with x hVx hVxpos
      constructor
      · exact div_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg _)) hVxpos.le
      · exact div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg x) (sq_nonneg _)) hVbase hVx
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper'
    · exact hbounds.mono fun x hx => hx.1
    · exact hbounds.mono fun x hx => hx.2
  have hscaled : Tendsto (fun x : ℝ => x ^ 2 * D x / V x)
      atTop (nhds 1) := by
    have hdecomp : (fun x : ℝ => x ^ 2 * D x / V x) =ᶠ[atTop]
        fun x => 2 * x ^ 2 * Q x / V x -
          x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x := by
      filter_upwards [] with x
      have hid := one_sub_norm_charFun_sq_eq_two_cosineDefect_sub_norm_sq ν (x⁻¹)
      dsimp [D, Q, V]
      rw [hid]
      ring
    have htemp := hcos.sub herror
    simpa using htemp.congr' hdecomp.symm
  have hDpos : ∀ᶠ x : ℝ in atTop, 0 < D x := by
    let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
      (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
    have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
    simpa [D] using tendsto_inv_atTop_nhdsGT_zero.eventually hpos
  have hscaledInv := hscaled.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvEq : (fun x : ℝ => (x ^ 2 * D x / V x)⁻¹) =ᶠ[atTop]
      fun x => V x / (x ^ 2 * D x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos, hDpos]
      with x hx hVx hDx
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
    have hDx' : D x ≠ 0 := hDx.ne'
    have hVx' : V x ≠ 0 := hVx.ne'
    field_simp [hx2, hDx', hVx']
  simpa [V] using hscaledInv.congr' hinvEq

/-- A centered integrable law in the standard Gaussian domain of attraction
has the exponent-two stable norming relation, including when its second
moment is infinite. -/
theorem IsInDomainOfAttractionAlong.isStableNorming_two_of_integrable_centered
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hscalePos : ∀ n, 0 < n → 0 < scale n) :
    IsStableNorming 2 ν scale := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hscaleTop : Tendsto scale atTop atTop := h.tendsto_scale_atTop hlimit
  have hdefect : Tendsto
      (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))
      atTop (nhds 1) := h.gaussian_defect_data.2.2
  have hcompat :=
    h.tendsto_truncatedSecondMoment_div_scaledNormDefect_of_gaussian_of_integrable_centered
      hint hmean
  have hcompatSeq : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)))
      atTop (nhds 1) := hcompat.comp hscaleTop
  have hproduct := hcompatSeq.mul hdefect
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hdefectEq : (fun n : ℕ =>
      truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) *
        ((n : ℝ) * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))) =ᶠ[atTop]
      fun n => (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 := by
    filter_upwards [h.eventually_scale_pos, hnatPos,
      hdefect.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hsn hnn hdn
    have hsn' : scale n ≠ 0 := ne_of_gt hsn
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hnn
    have hd : 1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hdn
      norm_num at hdn
    field_simp [hsn', hnn', hd]
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) * truncatedSecondMoment ν (scale n) /
        scale n ^ 2) atTop (nhds 1) := by
    simpa using hproduct.congr' hdefectEq
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 > 0 :=
    hratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hmomentPos : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (scale n) := by
    filter_upwards [hratioPos, hnatPos, h.eventually_scale_pos]
      with n hq hn hsn
    have hnum : 0 < (n : ℝ) * truncatedSecondMoment ν (scale n) :=
      (div_pos_iff_of_pos_right (sq_pos_of_pos hsn)).mp hq
    exact (mul_pos_iff_of_pos_left hn).mp hnum
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvEq : (fun n : ℕ =>
      ((n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2)⁻¹) =ᶠ[atTop]
      fun n => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ) := by
    filter_upwards [hmomentPos, hnatPos, h.eventually_scale_pos] with n hmoment hn hsn
    have hpow : scale n ^ (2 : ℝ) = scale n ^ (2 : ℕ) :=
      Real.rpow_natCast (scale n) 2
    rw [hpow]
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hmoment.ne', hnn']
  have hnormRatio : Tendsto
      (fun n : ℕ => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ))
      atTop (nhds 1) := by
    simpa using hinv.congr' hinvEq
  refine ⟨hscalePos, hscaleTop, ?_⟩
  simpa only [stableSlowVariation_two] using hnormRatio

/-- An uncentered Gaussian-domain normalization is the quadratic stable
norming, including in the infinite-variance case. The attraction hypothesis
implies first-moment integrability and zero mean; only positivity at the
finitely many initial indices is stated explicitly. -/
theorem IsInDomainOfAttractionAlong.isStableNorming_two_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n) :
    IsStableNorming 2 ν scale := by
  exact h.isStableNorming_two_of_integrable_centered
    h.integrable_id_of_gaussian h.integral_eq_zero_of_gaussian hscalePos

/-- Along a centered Gaussian-domain norming sequence, every fixed positive
multiple of the cutoff has the same normalized truncated-variance profile.
This is the triangular-array variance input for the exponent-two path limit. -/
theorem IsInDomainOfAttractionAlong.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      truncatedSecondMoment ν (c * scale n) / scale n ^ 2)
      atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hnorm : IsStableNorming 2 ν scale :=
    h.isStableNorming_two_of_gaussian hscalePos
  have hbase := hnorm.tendsto_nat_mul_truncatedSecondMoment_div_sq
  have hratio := h.truncatedSecondMoment_isSlowlyVarying_of_gaussian.ratio_tendsto hc
  have hratioSeq := hratio.comp hnorm.2.1
  have hbasePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  have hVpos : ∀ᶠ n : ℕ in atTop, 0 < V (scale n) :=
    hnorm.2.1.eventually h.eventually_pos_truncatedSecondMoment_of_gaussian
  have heq : (fun n : ℕ =>
      ((n : ℝ) * V (scale n) / scale n ^ 2) *
        (V (c * scale n) / V (scale n))) =ᶠ[atTop]
      fun n => (n : ℝ) * V (c * scale n) / scale n ^ 2 := by
    filter_upwards [hbasePos, hVpos] with n hb hV
    field_simp [ne_of_gt hb, ne_of_gt hV]
  have hresult := hbase.mul hratioSeq
  simpa [Real.rpow_zero, V] using hresult.congr' heq

/-- Under centered Gaussian attraction, the expected number of increments
larger than any fixed multiple of the norming scale tends to zero. This is the
Feller-tail input that removes macroscopic jumps in the exponent-two path
limit, including for infinite-variance laws. -/
theorem IsInDomainOfAttractionAlong.tendsto_nat_mul_twoSidedTail_mul_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x : ℝ | c * scale n < |x|}) atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let F : ℝ → ℝ := fun x => x ^ 2 * tail x / V x
  have hnorm : IsStableNorming 2 ν scale :=
    h.isStableNorming_two_of_gaussian hscalePos
  have hprofile := h.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
    hscalePos c hc
  have hscaleTop : Tendsto scale atTop atTop := hnorm.2.1
  have hscaledTop : Tendsto (fun n : ℕ => c * scale n) atTop atTop :=
    (tendsto_id.const_mul_atTop hc).comp hscaleTop
  have hF := h.tendsto_secondTailRatio_of_gaussian
  have hFseq := hF.comp hscaledTop
  have hFdiv : Tendsto (fun n : ℕ => F (c * scale n) / c ^ 2)
      atTop (nhds 0) := by
    simpa [F, tail] using hFseq.div_const (c ^ 2)
  have hVpos : ∀ᶠ n : ℕ in atTop, 0 < V (c * scale n) :=
    hscaledTop.eventually h.eventually_pos_truncatedSecondMoment_of_gaussian
  have hscalePosSeq : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have heq : (fun n : ℕ =>
      ((n : ℝ) * V (c * scale n) / scale n ^ 2) *
        (F (c * scale n) / c ^ 2)) =ᶠ[atTop]
      fun n => (n : ℝ) * tail (c * scale n) := by
    filter_upwards [hVpos, hscalePosSeq] with n hV hb
    dsimp [F, tail, V]
    field_simp [ne_of_gt hc, ne_of_gt hV, ne_of_gt hb]
    calc
      _ = (n : ℝ) * ν.real {x : ℝ | c * scale n < |x|} *
          (truncatedSecondMoment ν (c * scale n) *
            (truncatedSecondMoment ν (c * scale n))⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hV), mul_one]
  have hresult := hprofile.mul hFdiv
  simpa only [mul_zero, zero_mul] using hresult.congr' heq

end ProbabilityTheory

end
