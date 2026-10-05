/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Uniform

/-!
# Sequential asymptotic inversion for monotone regularly varying functions

This file states the regularity hypotheses required by the inversion result.
Pointwise ratio limits without monotonicity or another compact-uniformity
hypothesis are not used as if they implied uniform convergence.
-/

open Filter Set
open scoped Topology

@[expose] public section

namespace Asymptotics.IsRegularlyVaryingAtTop

/-- If `f` is eventually nondecreasing and regularly varying with positive
index, then a convergent ratio of its values identifies the ratio of the
arguments. The compact-uniform theorem supplies the final identification once
monotonicity has confined the argument ratios to a compact positive interval. -/
theorem tendsto_div_of_tendsto_value_ratio
    {f : ℝ → ℝ} {ρ r : ℝ} {x y : ℕ → ℝ}
    (hreg : IsRegularlyVaryingAtTop f ρ)
    (hmono : IsEventuallyMonotoneAtTop f)
    (hρ : 0 < ρ) (hr : 0 < r)
    (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hvalue : Tendsto (fun n => f (y n) / f (x n)) atTop (𝓝 (r ^ ρ))) :
    Tendsto (fun n => y n / x n) atTop (𝓝 r) := by
  obtain ⟨R, hR⟩ := hmono
  let l : ℝ := r / 2
  let u : ℝ := 2 * r
  have hl : 0 < l := by dsimp [l]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hlr : l < r := by dsimp [l]; linarith
  have hru : r < u := by dsimp [u]; linarith
  have hlpow : l ^ ρ < r ^ ρ := by
    exact Real.rpow_lt_rpow (le_of_lt hl) hlr hρ
  have hpowu : r ^ ρ < u ^ ρ := by
    exact Real.rpow_lt_rpow (le_of_lt hr) hru hρ
  have hden : ∀ᶠ n : ℕ in atTop, 0 < f (x n) :=
    hx.eventually hreg.eventually_pos
  have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n :=
    hx.eventually (eventually_gt_atTop 0)
  have hRx : ∀ᶠ n : ℕ in atTop, R ≤ x n :=
    hx.eventually (eventually_ge_atTop R)
  have hRy : ∀ᶠ n : ℕ in atTop, R ≤ y n :=
    hy.eventually (eventually_ge_atTop R)
  have hlx : ∀ᶠ n : ℕ in atTop, R ≤ l * x n := by
    exact ((tendsto_id.const_mul_atTop hl).comp hx).eventually
      (eventually_ge_atTop R)
  have hux : ∀ᶠ n : ℕ in atTop, R ≤ u * x n := by
    exact ((tendsto_id.const_mul_atTop hu).comp hx).eventually
      (eventually_ge_atTop R)
  have hlowdiff : Tendsto
      (fun n => f (y n) / f (x n) - f (l * x n) / f (x n)) atTop
      (𝓝 (r ^ ρ - l ^ ρ)) := by
    exact hvalue.sub ((hreg.ratio_tendsto hl).comp hx)
  have hlowpos : ∀ᶠ n : ℕ in atTop,
      0 < f (y n) / f (x n) - f (l * x n) / f (x n) :=
    hlowdiff.eventually (Ioi_mem_nhds (sub_pos.mpr hlpow))
  have hupdiff : Tendsto
      (fun n => f (u * x n) / f (x n) - f (y n) / f (x n)) atTop
      (𝓝 (u ^ ρ - r ^ ρ)) := by
    exact ((hreg.ratio_tendsto hu).comp hx).sub hvalue
  have huppos : ∀ᶠ n : ℕ in atTop,
      0 < f (u * x n) / f (x n) - f (y n) / f (x n) :=
    hupdiff.eventually (Ioi_mem_nhds (sub_pos.mpr hpowu))
  have hbounds : ∀ᶠ n : ℕ in atTop, l < y n / x n ∧ y n / x n < u := by
    filter_upwards [hden, hxpos, hRy, hlx, hux, hlowpos, huppos]
      with n hden hn hRy hlx hux hlow huppos
    constructor
    · by_contra hnot
      have hratio : y n / x n ≤ l := le_of_not_gt hnot
      have hmul : y n ≤ l * x n := (div_le_iff₀ hn).1 hratio
      have hmono : f (y n) ≤ f (l * x n) := hR hRy hmul
      have hquot : f (y n) / f (x n) ≤ f (l * x n) / f (x n) :=
        div_le_div_of_nonneg_right hmono hden.le
      linarith
    · by_contra hnot
      have hratio : u ≤ y n / x n := le_of_not_gt hnot
      have hmul : u * x n ≤ y n := (le_div_iff₀ hn).1 hratio
      have hmono : f (u * x n) ≤ f (y n) := hR hux hmul
      have hquot : f (u * x n) / f (x n) ≤ f (y n) / f (x n) :=
        div_le_div_of_nonneg_right hmono hden.le
      linarith
  have hratioPower : Tendsto (fun n => (y n / x n) ^ ρ) atTop (𝓝 (r ^ ρ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hvalueClose : ∀ᶠ n : ℕ in atTop,
        dist (f (y n) / f (x n)) (r ^ ρ) < ε / 2 := by
      have h := (Metric.tendsto_atTop.1 hvalue) (ε / 2) (by positivity)
      simpa using h
    have huniform : ∀ᶠ n : ℕ in atTop, ∀ c ∈ Set.Icc l u,
        dist (c ^ ρ) (f (c * x n) / f (x n)) < ε / 2 := by
      have hU := tendstoUniformlyOn_ratio_of_eventuallyMonotone
        hreg ⟨R, hR⟩ hl (le_of_lt (lt_trans hlr hru))
      have h := (Metric.tendstoUniformlyOn_iff.mp hU) (ε / 2) (by positivity)
      exact hx.eventually h
    obtain ⟨Nval, hNval⟩ := eventually_atTop.1 hvalueClose
    obtain ⟨NU, hNU⟩ := eventually_atTop.1 huniform
    obtain ⟨Nbounds, hNbounds⟩ := eventually_atTop.1 hbounds
    obtain ⟨Nxpos, hNxpos⟩ := eventually_atTop.1 hxpos
    refine ⟨max Nval (max NU (max Nbounds Nxpos)), ?_⟩
    intro n hn
    have hval := hNval n (le_trans (le_max_left _ _) hn)
    have hbound := hNbounds n (le_trans (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))) hn)
    have hpos := hNxpos n (le_trans (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))) hn)
    have hU := hNU n (le_trans (le_max_of_le_right (le_max_left _ _)) hn)
    have hmul : (y n / x n) * x n = y n := div_mul_cancel₀ _ (ne_of_gt hpos)
    have happrox : dist ((y n / x n) ^ ρ) (f (y n) / f (x n)) < ε / 2 := by
      simpa [hmul] using hU (y n / x n)
        ⟨le_of_lt hbound.1, le_of_lt hbound.2⟩
    calc
      dist ((y n / x n) ^ ρ) (r ^ ρ) ≤
          dist ((y n / x n) ^ ρ) (f (y n) / f (x n)) +
            dist (f (y n) / f (x n)) (r ^ ρ) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add happrox hval
      _ = ε := by ring
  have hroot : Tendsto (fun n => ((y n / x n) ^ ρ) ^ (1 / ρ)) atTop (𝓝 r) := by
    have h := hratioPower.rpow_const
      (x := r ^ ρ) (p := 1 / ρ) (Or.inl (ne_of_gt (Real.rpow_pos_of_pos hr ρ)))
    have hrEq : (r ^ ρ) ^ (1 / ρ) = r := by
      rw [← Real.rpow_mul (le_of_lt hr), mul_one_div_cancel hρ.ne', Real.rpow_one]
    rw [← hrEq]
    exact h
  have heq : (fun n => ((y n / x n) ^ ρ) ^ (1 / ρ)) =ᶠ[atTop]
      fun n => y n / x n := by
    filter_upwards [hbounds] with n hn
    have hpos : 0 < y n / x n := lt_trans hl hn.1
    rw [← Real.rpow_mul (le_of_lt hpos), mul_one_div_cancel hρ.ne', Real.rpow_one]
  exact hroot.congr' heq

/-- Sequential inversion for the quotient `x ^ 2 / V x` when `V` is an
eventually nondecreasing regularly varying function of index below two. The
monotonicity and the Potter bound are applied to `V`; no monotonicity is
assumed for the quotient itself. -/
theorem tendsto_div_of_tendsto_squareQuotient_ratio
    {V : ℝ → ℝ} {β r : ℝ} {x y : ℕ → ℝ}
    (hV : IsRegularlyVaryingAtTop V β)
    (hVmono : IsEventuallyMonotoneAtTop V)
    (hβ : 0 ≤ β) (hβ₂ : β < 2) (hr : 0 < r)
    (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hquotient : Tendsto
      (fun n => (y n) ^ 2 / V (y n) / ((x n) ^ 2 / V (x n))) atTop
      (𝓝 (r ^ (2 - β)))) :
    Tendsto (fun n => y n / x n) atTop (𝓝 r) := by
  let α : ℝ := 2 - β
  let γ : ℝ := α / 2
  let p : ℝ := β + γ
  let C : ℝ := 2 ^ p
  let limit : ℝ := r ^ α
  have hα : 0 < α := by dsimp [α]; linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγp : 2 - p = γ := by dsimp [α, γ, p]; ring
  have hC : 0 < C := by dsimp [C]; positivity
  have hlimit : 0 < limit := by
    dsimp [limit]
    exact Real.rpow_pos_of_pos hr α
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hV.exists_potter_upper_bound (ε := γ) hVmono hβ hγ
  let lowerBase : ℝ :=
    (limit / (2 * C)) ^ (1 / γ)
  let upperBase : ℝ :=
    (C * (limit + 1)) ^ (1 / γ)
  let lower : ℝ := min 1 lowerBase
  let upper : ℝ := max 1 upperBase
  have hlowerArg : 0 < limit / (2 * C) := by positivity
  have hupperArg : 0 < C * (limit + 1) := by positivity
  have hlowerBase : 0 < lowerBase := by
    dsimp [lowerBase]
    exact Real.rpow_pos_of_pos hlowerArg _
  have hupperBase : 0 < upperBase := by
    dsimp [upperBase]
    exact Real.rpow_pos_of_pos hupperArg _
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hupper : 0 < upper := by dsimp [upper]; positivity
  have hcompactRatio : ∀ᶠ n : ℕ in atTop,
      lower ≤ y n / x n ∧ y n / x n ≤ upper := by
    have hRx : ∀ᶠ n : ℕ in atTop, Rpotter ≤ x n :=
      hx.eventually (eventually_ge_atTop Rpotter)
    have hRy : ∀ᶠ n : ℕ in atTop, Rpotter ≤ y n :=
      hy.eventually (eventually_ge_atTop Rpotter)
    have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n :=
      hx.eventually (eventually_gt_atTop 0)
    have hypos : ∀ᶠ n : ℕ in atTop, 0 < y n :=
      hy.eventually (eventually_gt_atTop 0)
    have hVxpos : ∀ᶠ n : ℕ in atTop, 0 < V (x n) :=
      hx.eventually hV.eventually_pos
    have hVypos : ∀ᶠ n : ℕ in atTop, 0 < V (y n) :=
      hy.eventually hV.eventually_pos
    have hquotientWindow : ∀ᶠ n : ℕ in atTop,
        y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) ∈
          Set.Ioo (limit / 2) (limit + 1) := by
      have hmem : Set.Ioo (limit / 2) (limit + 1) ∈ 𝓝 limit :=
        isOpen_Ioo.mem_nhds ⟨by linarith [hlimit], by linarith⟩
      exact hquotient.eventually hmem
    filter_upwards [hRx, hRy, hxpos, hypos, hVxpos, hVypos,
      hquotientWindow] with n hRx hRy hxpos hypos hVxpos hVypos hwindow
    let ratio : ℝ := y n / x n
    have hratio : 0 < ratio := by dsimp [ratio]; exact div_pos hypos hxpos
    have hratioFormula :
        y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) =
          ratio ^ 2 / (V (y n) / V (x n)) := by
      dsimp [ratio]
      field_simp [ne_of_gt hxpos, ne_of_gt hVxpos, ne_of_gt hVypos]
    have hlowBasePow : lowerBase ^ γ = limit / (2 * C) := by
      dsimp [lowerBase]
      rw [← Real.rpow_mul (le_of_lt hlowerArg), one_div_mul_cancel hγ.ne',
        Real.rpow_one]
    have hupBasePow : upperBase ^ γ = C * (limit + 1) := by
      dsimp [upperBase]
      rw [← Real.rpow_mul (le_of_lt hupperArg), one_div_mul_cancel hγ.ne',
        Real.rpow_one]
    by_cases hratioone : 1 ≤ ratio
    · have hxy : x n ≤ y n := (one_le_div₀ hxpos).1 (by simpa [ratio] using hratioone)
      have hpot := hpotter hRx hxy
      have hratioUpper : V (y n) / V (x n) ≤ C * ratio ^ p := by
        simpa [C, p, ratio, mul_comm] using hpot
      have hquotientLower : ratio ^ γ / C ≤
          y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) := by
        rw [hratioFormula]
        apply (le_div_iff₀ (div_pos hVypos hVxpos)).2
        calc
          ratio ^ γ / C * (V (y n) / V (x n)) ≤
              ratio ^ γ / C * (C * ratio ^ p) :=
                mul_le_mul_of_nonneg_left hratioUpper (by positivity)
          _ = ratio ^ (γ + p) := by
            rw [div_mul_eq_mul_div]
            dsimp [C]
            field_simp
            exact (Real.rpow_add hratio γ p).symm
          _ = ratio ^ 2 := by
            rw [show γ + p = 2 by linarith [hγp]]
            exact Real.rpow_natCast ratio 2
      have hratiopower : ratio ^ γ < C * (limit + 1) := by
        have hle : ratio ^ γ ≤ C * (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) := by
          calc
            ratio ^ γ = C * (ratio ^ γ / C) := by field_simp [ne_of_gt hC]
            _ ≤ C * (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) :=
              mul_le_mul_of_nonneg_left hquotientLower hC.le
        exact lt_of_le_of_lt hle (mul_lt_mul_of_pos_left hwindow.2 hC)
      have hratioUpper : ratio < upperBase := by
        simpa [upperBase] using
          (Real.lt_rpow_inv_iff_of_pos hratio.le (le_of_lt hupperArg) hγ).2 hratiopower
      have hupperBound : ratio ≤ upper := by
        dsimp [upper]
        exact le_trans (le_of_lt hratioUpper) (le_max_right _ _)
      have hlowerBound : lower ≤ ratio := by
        dsimp [lower]
        by_cases hbase : lowerBase ≤ 1
        · rw [min_eq_right hbase]
          exact hbase.trans hratioone
        · rw [min_eq_left (le_of_not_ge hbase)]
          exact hratioone
      exact ⟨hlowerBound, hupperBound⟩
    · have hratiole : ratio ≤ 1 := le_of_not_ge hratioone
      have hyx : y n ≤ x n := by
        have hdiv : y n / x n ≤ 1 := by simpa [ratio] using hratiole
        have hmul := (div_le_iff₀ hxpos).1 hdiv
        nlinarith
      have hpot := hpotter hRy hyx
      have hinv : x n / y n = ratio⁻¹ := by
        dsimp [ratio]
        field_simp [ne_of_gt hxpos, ne_of_gt hypos]
      have hratioUpper : V (x n) / V (y n) ≤ C * ratio ^ (-p) := by
        have hpot' : V (x n) / V (y n) ≤ C * (x n / y n) ^ p := by
          simpa [C, p] using hpot
        have hpowInv : ratio⁻¹ ^ p = ratio ^ (-p) := by
          rw [Real.inv_rpow hratio.le, Real.rpow_neg hratio.le]
        rw [hinv, hpowInv] at hpot'
        exact hpot'
      have hquotientFormula :
          y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) =
            ratio ^ 2 * (V (x n) / V (y n)) := by
        dsimp [ratio]
        field_simp [ne_of_gt hxpos, ne_of_gt hypos,
          ne_of_gt hVxpos, ne_of_gt hVypos]
      have hpower : ratio ^ 2 * ratio ^ (-p) = ratio ^ γ := by
        calc
          ratio ^ 2 * ratio ^ (-p) = ratio ^ (2 : ℝ) * ratio ^ (-p) := by
            exact congrArg (fun z : ℝ => z * ratio ^ (-p))
              (Real.rpow_natCast ratio 2).symm
          _ = ratio ^ (2 : ℝ) / ratio ^ p := by
            rw [Real.rpow_neg hratio.le, div_eq_mul_inv]
          _ = ratio ^ (2 - p) := by
            exact (Real.rpow_sub hratio 2 p).symm
          _ = ratio ^ γ := by simp [hγp]
      have hquotientUpper :
          y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) ≤ C * ratio ^ γ := by
        calc
          y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) =
              ratio ^ 2 * (V (x n) / V (y n)) := hquotientFormula
          _ ≤ ratio ^ 2 * (C * ratio ^ (-p)) :=
            mul_le_mul_of_nonneg_left hratioUpper (sq_nonneg ratio)
          _ = C * (ratio ^ 2 * ratio ^ (-p)) := by ring
          _ = C * ratio ^ γ := by rw [hpower]
      have hratiopower : limit / (2 * C) < ratio ^ γ := by
        have hlt : limit / 2 < C * ratio ^ γ := lt_of_lt_of_le hwindow.1 hquotientUpper
        have hdiv : (limit / 2) / C < ratio ^ γ :=
          (div_lt_iff₀ hC).2 (by simpa [mul_comm] using hlt)
        have heq : (limit / 2) / C = limit / (2 * C) := by
          field_simp
        rw [heq] at hdiv
        exact hdiv
      have hratioLower : lowerBase < ratio :=
        by
          simpa [lowerBase] using
            (Real.rpow_inv_lt_iff_of_pos (le_of_lt hlowerArg) hratio.le hγ).2 hratiopower
      have hlowerBound : lower ≤ ratio := by
        dsimp [lower]
        exact le_trans (min_le_right _ _) hratioLower.le
      have hupperBound : ratio ≤ upper := by
        dsimp [upper]
        exact le_trans hratiole (le_max_left _ _)
      exact ⟨hlowerBound, hupperBound⟩
  have hVuniform : TendstoUniformlyOn
      (fun z c => V (c * z) / V z) (fun c => c ^ β)
      atTop (Set.Icc lower upper) :=
    hV.tendstoUniformlyOn_ratio_of_eventuallyMonotone hVmono hlower
      (calc
        lower ≤ 1 := min_le_left _ _
        _ ≤ upper := le_max_left _ _)
  have hlimitPower : Tendsto (fun n => (y n / x n) ^ α) atTop (𝓝 limit) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hvalueClose : ∀ᶠ n : ℕ in atTop,
        dist (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) limit < ε / 2 := by
      have h := (Metric.tendsto_atTop.1 hquotient) (ε / 2) (by positivity)
      simpa [limit, α] using h
    have hquotientUpper : ∀ᶠ n : ℕ in atTop,
        y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) < limit + 1 := by
      have hnbhd : Set.Iio (limit + 1) ∈ 𝓝 limit := Iio_mem_nhds (by linarith)
      exact hquotient.eventually hnbhd
    let d : ℝ := lower ^ β
    let δ : ℝ := ε * d / (4 * (limit + 1))
    have hd : 0 < d := by dsimp [d]; exact Real.rpow_pos_of_pos hlower β
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have huniform : ∀ᶠ n : ℕ in atTop, ∀ c ∈ Set.Icc lower upper,
        dist (c ^ β) (V (c * x n) / V (x n)) < δ := by
      have h := (Metric.tendstoUniformlyOn_iff.mp hVuniform) δ hδ
      exact hx.eventually h
    have hclose : ∀ᶠ n : ℕ in atTop,
        dist ((y n / x n) ^ α) limit < ε := by
      filter_upwards [hvalueClose, hquotientUpper, huniform, hcompactRatio,
        hx.eventually (eventually_gt_atTop 0),
        hy.eventually (eventually_gt_atTop 0),
        hx.eventually hV.eventually_pos, hy.eventually hV.eventually_pos]
        with n hval hκupper hU hbound hxpos hypos hVxpos hVypos
      let ratio : ℝ := y n / x n
      have hratio : 0 < ratio := by dsimp [ratio]; exact div_pos hypos hxpos
      have hratioβLower : d ≤ ratio ^ β := by
        dsimp [d]
        exact Real.rpow_le_rpow (le_of_lt hlower) hbound.1 hβ
      have hVratio : V (y n) / V (x n) = V (ratio * x n) / V (x n) := by
        have hmul : ratio * x n = y n := div_mul_cancel₀ _ (ne_of_gt hxpos)
        rw [hmul]
      have hVclose : |V (y n) / V (x n) - ratio ^ β| < δ := by
        have hdist := hU ratio hbound
        have hmul : ratio * x n = y n := div_mul_cancel₀ _ (ne_of_gt hxpos)
        rw [Real.dist_eq, abs_sub_comm] at hdist
        simpa [hVratio] using hdist
      have hformula :
          y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) *
            (V (y n) / V (x n)) = ratio ^ 2 := by
        dsimp [ratio]
        field_simp [ne_of_gt hxpos, ne_of_gt hypos,
          ne_of_gt hVxpos, ne_of_gt hVypos]
      have hpower : ratio ^ β * ratio ^ α = ratio ^ 2 := by
        calc
          ratio ^ β * ratio ^ α = ratio ^ (β + α) := (Real.rpow_add hratio β α).symm
          _ = ratio ^ (2 : ℝ) := by
            rw [show β + α = (2 : ℝ) by dsimp [α]; ring]
          _ = ratio ^ 2 := Real.rpow_natCast ratio 2
      have hid : ratio ^ β * (ratio ^ α -
            (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))) =
          (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
            (V (y n) / V (x n) - ratio ^ β) := by
        nlinarith [hformula, hpower]
      have hκpos : 0 < y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)) := by
        positivity
      have habsId : ratio ^ β * |ratio ^ α -
            (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| =
          (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
            |V (y n) / V (x n) - ratio ^ β| := by
        calc
          ratio ^ β * |ratio ^ α -
              (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| =
              |ratio ^ β * (ratio ^ α -
                (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))))| := by
                  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hratio.le _)]
          _ = |(y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
                (V (y n) / V (x n) - ratio ^ β)| := congrArg abs hid
          _ = (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
                |V (y n) / V (x n) - ratio ^ β| := by
                  rw [abs_mul, abs_of_nonneg hκpos.le]
      have habsSmall : |ratio ^ α -
          (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| < ε / 4 := by
        have hupperAbs :
            (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
                |V (y n) / V (x n) - ratio ^ β| < (limit + 1) * δ := by
          calc
            _ < (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) * δ :=
              mul_lt_mul_of_pos_left hVclose (by positivity)
            _ ≤ (limit + 1) * δ :=
              mul_le_mul_of_nonneg_right hκupper.le hδ.le
        have hmainAbs : d * |ratio ^ α -
            (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| < (limit + 1) * δ := by
          calc
            d * |ratio ^ α -
                (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| ≤
                ratio ^ β * |ratio ^ α -
                  (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| :=
                    mul_le_mul_of_nonneg_right hratioβLower (abs_nonneg _)
            _ = (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) *
                  |V (y n) / V (x n) - ratio ^ β| := habsId
            _ < (limit + 1) * δ := hupperAbs
        have hcancel : (limit + 1) * δ = ε * d / 4 := by
          dsimp [δ]
          have hpos : 0 < limit + 1 := by linarith
          field_simp
        rw [hcancel] at hmainAbs
        have : |ratio ^ α -
            (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| < ε / 4 := by
          by_contra hnot
          have hge : ε / 4 ≤ |ratio ^ α -
              (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n)))| := le_of_not_gt hnot
          have hmul := mul_le_mul_of_nonneg_left hge hd.le
          nlinarith
        exact this
      have hdistApprox : dist (ratio ^ α)
          (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) < ε / 4 := by
        rw [Real.dist_eq]
        exact habsSmall
      have hdist : dist (ratio ^ α) limit < ε := by
        calc
          dist (ratio ^ α) limit ≤
                dist (ratio ^ α) (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) +
                dist (y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) limit :=
              dist_triangle _ _ _
          _ < ε / 4 + ε / 2 := add_lt_add hdistApprox hval
          _ < ε := by linarith
      simpa [ratio] using hdist
    obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
    exact ⟨N, hN⟩
  have hroot : Tendsto (fun n => ((y n / x n) ^ α) ^ (1 / α)) atTop (𝓝 r) := by
    have h := hlimitPower.rpow_const
      (x := limit) (p := 1 / α) (Or.inl hlimit.ne')
    have hrEq : limit ^ (1 / α) = r := by
      dsimp [limit, α]
      rw [← Real.rpow_mul (le_of_lt hr), mul_one_div_cancel hα.ne', Real.rpow_one]
    rw [← hrEq]
    exact h
  have heq : (fun n => ((y n / x n) ^ α) ^ (1 / α)) =ᶠ[atTop]
      fun n => y n / x n := by
    filter_upwards [hcompactRatio] with n hn
    have hratio : 0 < y n / x n := lt_of_lt_of_le hlower hn.1
    rw [← Real.rpow_mul (le_of_lt hratio), mul_one_div_cancel hα.ne', Real.rpow_one]
  exact hroot.congr' heq

end Asymptotics.IsRegularlyVaryingAtTop

end
