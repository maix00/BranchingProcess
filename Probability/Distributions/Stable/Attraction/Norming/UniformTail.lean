/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Uniform
public import Probability.Distributions.Stable.Attraction.Norming.Tail

/-!
# Uniform tail limits along stable normings

The fixed-multiple tail asymptotic is uniform when the multiplier ranges in a
compact interval bounded away from zero. This is the uniform input needed when
truncation thresholds vary inside a local block estimate.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- Along a stable norming sequence, the regularly varying two-sided tail
limit is uniform on every compact interval of positive multipliers. The
compact-uniform convergence theorem is applied to the reciprocal tail, which
is eventually nondecreasing. -/
theorem IsStableNorming.tendstoUniformlyOn_nat_mul_twoSidedTail_mul_of_regularlyVarying
    {α a b : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun (n : ℕ) (c : ℝ) =>
        (n : ℝ) * ν.real {x : ℝ | c * normalization n < |x|})
      (fun c => ((2 - α) / α) * c ^ (-α))
      atTop (Set.Icc a b) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let inverseTail : ℝ → ℝ := fun u => (tail u)⁻¹
  let multipliers : Set ℝ := Set.Icc a b
  have htailPos : ∀ᶠ u : ℝ in atTop, 0 < tail u := by
    simpa [tail] using htail.eventually_pos
  obtain ⟨R, hR⟩ := eventually_atTop.1 htailPos
  have hinverseRV : Asymptotics.IsRegularlyVaryingAtTop inverseTail α := by
    simpa [inverseTail, tail] using htail.inv
  have hinverseMono : Asymptotics.IsEventuallyMonotoneAtTop inverseTail := by
    refine ⟨R, ?_⟩
    intro x y hx hxy
    have hxpos : 0 < tail x := hR x hx
    have hypos : 0 < tail y := hR y (le_trans hx hxy)
    have hsets : {z : ℝ | y < |z|} ⊆ {z : ℝ | x < |z|} := by
      intro z hz
      exact lt_of_le_of_lt hxy hz
    have htailAnti : tail y ≤ tail x := by
      exact measureReal_mono hsets
    change (tail x)⁻¹ ≤ (tail y)⁻¹
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hypos htailAnti

  have hratioUniform : TendstoUniformlyOn
      (fun n c => inverseTail (c * normalization n) /
        inverseTail (normalization n))
      (fun c => c ^ α) atTop multipliers := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hratio := hinverseRV.tendstoUniformlyOn_ratio_of_eventuallyMonotone
      hinverseMono ha hab
    obtain ⟨S, hS⟩ := eventually_atTop.1 <|
      (Metric.tendstoUniformlyOn_iff.mp hratio) ε hε
    have hscale := hnorm.2.1.eventually (eventually_ge_atTop S)
    filter_upwards [hscale] with n hn c hc
    exact hS (normalization n) hn c hc

  let lowerLimit : ℝ := a ^ α
  let inverseLower : ℝ := lowerLimit / 2
  have hlowerLimit : 0 < lowerLimit := by
    dsimp [lowerLimit]
    exact Real.rpow_pos_of_pos ha α
  have hinverseLower : 0 < inverseLower := by
    dsimp [inverseLower]
    positivity
  have hratioInverseUniform : TendstoUniformlyOn
      (fun n c => (inverseTail (c * normalization n) /
        inverseTail (normalization n))⁻¹)
      (fun c => (c ^ α)⁻¹) atTop multipliers := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hclose := (Metric.tendstoUniformlyOn_iff.mp hratioUniform)
      inverseLower hinverseLower
    let δ : ℝ := ε * inverseLower ^ 2 / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcloseSmall := (Metric.tendstoUniformlyOn_iff.mp hratioUniform) δ hδ
    have hlowerAt : ∀ c ∈ multipliers, lowerLimit ≤ c ^ α := by
      intro c hc
      have hac : a ≤ c := hc.1
      dsimp [lowerLimit]
      exact Real.rpow_le_rpow (le_of_lt ha) hac (le_of_lt hα₀)
    have hargPosEventually : ∀ᶠ n : ℕ in atTop, 0 < a * normalization n := by
      have hmul := (tendsto_id.const_mul_atTop ha).comp hnorm.2.1
      exact hmul.eventually (eventually_gt_atTop 0)
    have htailAtScale : ∀ᶠ n : ℕ in atTop, R ≤ a * normalization n := by
      have hmul := (tendsto_id.const_mul_atTop ha).comp hnorm.2.1
      exact hmul.eventually (eventually_ge_atTop R)
    have hbaseTailEventually : ∀ᶠ n : ℕ in atTop, R ≤ normalization n :=
      hnorm.2.1.eventually (eventually_ge_atTop R)
    filter_upwards [hclose, hcloseSmall, hargPosEventually, htailAtScale,
      hbaseTailEventually] with n hcloseAt hsmall hapos haR hbaseR c hc
    have hbaseTail : 0 < tail (normalization n) := by
      exact hR (normalization n) hbaseR
    have hscaledTail : 0 < tail (c * normalization n) := by
      apply hR
      have hca : a ≤ c := hc.1
      have hnormpos : 0 < normalization n :=
        (mul_pos_iff_of_pos_left ha).mp hapos
      have hmul : a * normalization n ≤ c * normalization n :=
        mul_le_mul_of_nonneg_right hca (le_of_lt hnormpos)
      exact le_trans haR hmul
    have hx : 0 < inverseTail (c * normalization n) /
        inverseTail (normalization n) := by
      exact div_pos (inv_pos.mpr hscaledTail) (inv_pos.mpr hbaseTail)
    have hy : 0 < c ^ α := Real.rpow_pos_of_pos (lt_of_lt_of_le ha hc.1) α
    have hleft : inverseLower ≤
        inverseTail (c * normalization n) / inverseTail (normalization n) := by
      have h := hcloseAt c hc
      have hlim := hlowerAt c hc
      rw [Real.dist_eq, abs_sub_comm] at h
      have hnear : |inverseTail (c * normalization n) /
          inverseTail (normalization n) - c ^ α| < inverseLower := by
        simpa [Real.dist_eq, abs_sub_comm, inverseLower, lowerLimit] using h
      have := abs_lt.mp hnear
      dsimp [inverseLower, lowerLimit] at *
      linarith [hlim]
    have hlimLower : inverseLower ≤ c ^ α := by
      dsimp [inverseLower, lowerLimit]
      linarith [hlowerAt c hc]
    have hformula : |(inverseTail (c * normalization n) /
        inverseTail (normalization n))⁻¹ - (c ^ α)⁻¹| =
        |inverseTail (c * normalization n) /
          inverseTail (normalization n) - c ^ α| /
          ((inverseTail (c * normalization n) /
            inverseTail (normalization n)) * c ^ α) := by
      calc
        _ = |(c ^ α - inverseTail (c * normalization n) /
            inverseTail (normalization n)) /
            ((inverseTail (c * normalization n) /
              inverseTail (normalization n)) * c ^ α)| := by
              rw [inv_sub_inv (ne_of_gt hx) (ne_of_gt hy)]
        _ = |inverseTail (c * normalization n) /
            inverseTail (normalization n) - c ^ α| /
            ((inverseTail (c * normalization n) /
              inverseTail (normalization n)) * c ^ α) := by
              rw [abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy, abs_sub_comm]
    have herror : |inverseTail (c * normalization n) /
        inverseTail (normalization n) - c ^ α| <
          ε * inverseLower ^ 2 / 2 := by
      have h := hsmall c hc
      rw [Real.dist_eq, abs_sub_comm] at h
      simpa [Real.dist_eq, abs_sub_comm, δ] using h
    have hdenom : inverseLower ^ 2 ≤
        (inverseTail (c * normalization n) / inverseTail (normalization n)) *
          c ^ α := by
      simpa [pow_two] using
        (mul_le_mul hleft hlimLower (le_of_lt hinverseLower) (le_of_lt hx))
    have hbound : |(inverseTail (c * normalization n) /
        inverseTail (normalization n))⁻¹ - (c ^ α)⁻¹| < ε := by
      rw [hformula]
      calc
        _ ≤ (ε * inverseLower ^ 2 / 2) /
            ((inverseTail (c * normalization n) / inverseTail (normalization n)) *
              c ^ α) :=
          div_le_div_of_nonneg_right (le_of_lt herror)
            (le_of_lt (mul_pos hx hy))
        _ < ε := by
          have hsq : inverseLower ^ 2 ≠ 0 :=
            ne_of_gt (sq_pos_of_pos hinverseLower)
          have hquot : (ε * inverseLower ^ 2 / 2) /
              ((inverseTail (c * normalization n) / inverseTail (normalization n)) * c ^ α) ≤ ε / 2 := by
            calc
              _ ≤ (ε * inverseLower ^ 2 / 2) / inverseLower ^ 2 :=
                div_le_div_of_nonneg_left (by positivity)
                  (sq_pos_of_pos hinverseLower) hdenom
              _ = ε / 2 := by field_simp [hsq]
          exact lt_of_le_of_lt hquot (by linarith)
    simpa only [Real.dist_eq, abs_sub_comm] using hbound

  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < tail (normalization n) :=
    hnorm.2.1.eventually htailPos
  have hargPosEventually : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    have hmul := (tendsto_id.const_mul_atTop ha).comp hnorm.2.1
    filter_upwards [hmul.eventually (eventually_gt_atTop 0)] with n hn
    exact (mul_pos_iff_of_pos_left ha).mp hn
  have htailAtScale : ∀ᶠ n : ℕ in atTop, R ≤ a * normalization n := by
    have hmul := (tendsto_id.const_mul_atTop ha).comp hnorm.2.1
    exact hmul.eventually (eventually_ge_atTop R)
  have hratioTailUniformInv : TendstoUniformlyOn
      (fun n c => tail (c * normalization n) / tail (normalization n))
      (fun c => (c ^ α)⁻¹) atTop multipliers := by
    refine hratioInverseUniform.congr ?_
    filter_upwards [hscalePos, htailAtScale, hargPosEventually]
      with n hbase haR hnpos c hc
    have hbase' : tail (normalization n) ≠ 0 := ne_of_gt hbase
    have hscaledPos : 0 < tail (c * normalization n) := by
      apply hR
      exact le_trans haR
        (mul_le_mul_of_nonneg_right hc.1 (le_of_lt hnpos))
    have hscaled' : tail (c * normalization n) ≠ 0 := ne_of_gt hscaledPos
    change (inverseTail (c * normalization n) / inverseTail (normalization n))⁻¹ = _
    dsimp [inverseTail]
    field_simp [hbase', hscaled']

  have hratioTailUniform : TendstoUniformlyOn
      (fun n c => tail (c * normalization n) / tail (normalization n))
      (fun c => c ^ (-α)) atTop multipliers :=
    hratioTailUniformInv.congr_right fun c hc => by
      change (c ^ α)⁻¹ = c ^ (-α)
      rw [← Real.rpow_neg (le_of_lt (lt_of_lt_of_le ha hc.1))]

  let base : ℕ → ℝ := fun n => (n : ℝ) * tail (normalization n)
  have hbaseLimit := hnorm.tendsto_nat_mul_twoSidedTail_of_regularlyVarying
    hα₀ hα₂ htail
  let constant : ℝ := (2 - α) / α
  have hbaseUniform : TendstoUniformlyOn
      (fun (n : ℕ) (_c : ℝ) => base n) (fun _c => constant)
      atTop multipliers := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hevent := hbaseLimit.eventually
      (Metric.ball_mem_nhds constant hε)
    filter_upwards [hevent] with n hn c hc
    simpa [base, constant, Real.dist_eq, abs_sub_comm] using hn
  let bound : ℝ := (a ^ α)⁻¹
  have hboundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have htargetBound : ∀ c ∈ multipliers, 0 ≤ c ^ (-α) ∧ c ^ (-α) ≤ bound := by
    intro c hc
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    have hpow : a ^ α ≤ c ^ α :=
      Real.rpow_le_rpow (le_of_lt ha) hc.1 (le_of_lt hα₀)
    constructor
    · positivity
    · dsimp [bound]
      rw [Real.rpow_neg (le_of_lt hcpos) α]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha α) hpow)
  have hproduct : TendstoUniformlyOn
      (fun n c => base n * (tail (c * normalization n) / tail (normalization n)))
      (fun c => constant * c ^ (-α)) atTop multipliers := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let ε₁ : ℝ := ε / (2 * (bound + 1))
    let ε₂ : ℝ := ε / (2 * (|constant| + 1))
    have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
    have hε₂ : 0 < ε₂ := by dsimp [ε₂]; positivity
    have hbaseNear := (Metric.tendstoUniformlyOn_iff.mp hbaseUniform) ε₁ hε₁
    have hratioNearOne := (Metric.tendstoUniformlyOn_iff.mp hratioTailUniform) 1 zero_lt_one
    have hratioNear := (Metric.tendstoUniformlyOn_iff.mp hratioTailUniform) ε₂ hε₂
    filter_upwards [hbaseNear, hratioNearOne, hratioNear] with n hbase hnear hratio c hc
    have hbaseErr : |base n - constant| < ε₁ := by
      have h := hbase c hc
      simpa [Real.dist_eq, abs_sub_comm] using h
    have hratioErr : |tail (c * normalization n) / tail (normalization n) -
        c ^ (-α)| < ε₂ := by
      have h := hratio c hc
      simpa [Real.dist_eq, abs_sub_comm] using h
    have hratioErrOne : |tail (c * normalization n) / tail (normalization n) -
        c ^ (-α)| < 1 := by
      have h := hnear c hc
      simpa [Real.dist_eq, abs_sub_comm] using h
    have hratioAbs : |tail (c * normalization n) / tail (normalization n)| ≤ bound + 1 := by
      calc
        _ = |(tail (c * normalization n) / tail (normalization n) - c ^ (-α)) +
            c ^ (-α)| := by congr 1; ring
        _ ≤ |tail (c * normalization n) / tail (normalization n) - c ^ (-α)| +
            |c ^ (-α)| := abs_add_le _ _
        _ ≤ 1 + bound := by
          have htb := (htargetBound c hc).2
          have htn := (htargetBound c hc).1
          rw [abs_of_nonneg htn]
          exact add_le_add (le_of_lt hratioErrOne) htb
        _ = bound + 1 := by ring
    have hprodIdentity : base n * (tail (c * normalization n) / tail (normalization n)) -
        constant * c ^ (-α) =
        (base n - constant) * (tail (c * normalization n) / tail (normalization n)) +
          constant * (tail (c * normalization n) / tail (normalization n) - c ^ (-α)) := by ring
    rw [Real.dist_eq, abs_sub_comm]
    calc
      _ = |(base n - constant) * (tail (c * normalization n) / tail (normalization n)) +
          constant * (tail (c * normalization n) / tail (normalization n) - c ^ (-α))| := by
        rw [hprodIdentity]
      _ ≤ |base n - constant| * |tail (c * normalization n) / tail (normalization n)| +
          |constant| * |tail (c * normalization n) / tail (normalization n) - c ^ (-α)| := by
        calc
          _ ≤ |(base n - constant) * (tail (c * normalization n) / tail (normalization n))| +
              |constant * (tail (c * normalization n) / tail (normalization n) - c ^ (-α))| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ < ε := by
        have hfirst : |base n - constant| *
            |tail (c * normalization n) / tail (normalization n)| < ε / 2 := by
          calc
            _ ≤ |base n - constant| * (bound + 1) :=
              mul_le_mul_of_nonneg_left hratioAbs (abs_nonneg _)
            _ < ε₁ * (bound + 1) := mul_lt_mul_of_pos_right hbaseErr
              (by positivity)
            _ = ε / 2 := by dsimp [ε₁]; field_simp
        have hsecond : |constant| *
            |tail (c * normalization n) / tail (normalization n) - c ^ (-α)| < ε / 2 := by
          calc
            _ ≤ (|constant| + 1) *
                |tail (c * normalization n) / tail (normalization n) - c ^ (-α)| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            _ < (|constant| + 1) * ε₂ :=
              mul_lt_mul_of_pos_left hratioErr (by positivity)
            _ = ε / 2 := by dsimp [ε₂]; field_simp
        nlinarith
  have hresult : TendstoUniformlyOn
      (fun (n : ℕ) c => (n : ℝ) * tail (c * normalization n))
      (fun c => constant * c ^ (-α)) atTop multipliers := by
    refine hproduct.congr ?_
    filter_upwards [hscalePos] with n hn c hc
    dsimp [base, constant]
    field_simp [ne_of_gt hn]

  simpa [tail, constant, multipliers] using hresult

end ProbabilityTheory

end
