/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Integral asymptotics for regularly varying tails

This file proves the integral form of Karamata's theorem needed for truncated
moments. The proof uses a Potter bound and dominated convergence.
-/

open Filter MeasureTheory Topology
open scoped Interval

@[expose] public section

namespace Asymptotics

/-- Karamata's integral theorem for a nonnegative monotone regularly varying
function with index greater than `-1`. The ratio is integrated after the
change of variables `t = s * U`; monotonicity gives the integrable constant
bound on `s ∈ (0, 1]`. -/
theorem IsRegularlyVaryingAtTop.tendsto_intervalIntegral_div_mul_of_monotone
    {g : ℝ → ℝ} {ρ : ℝ}
    (hreg : IsRegularlyVaryingAtTop g ρ)
    (hρ : -1 < ρ)
    (hmono : Monotone g)
    (hnonneg : ∀ x, 0 ≤ g x) :
    Tendsto (fun U : ℝ =>
      (∫ t in (0:ℝ)..U, g t) / (U * g U)) atTop
      (nhds (1 / (ρ + 1))) := by
  let F : ℝ → ℝ → ℝ := fun U s => g (s * U) / g U
  have hFmeas : ∀ᶠ U : ℝ in atTop,
      AEStronglyMeasurable (F U) (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [] with U
    have hmeas : Measurable (F U) := by
      dsimp [F]
      exact (hmono.measurable.comp (measurable_id.mul_const U)).div measurable_const
    exact hmeas.aestronglyMeasurable
  have hbound : ∀ᶠ U : ℝ in atTop, ∀ᵐ s ∂volume,
      s ∈ Ι (0:ℝ) 1 → ‖F U s‖ ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hreg.eventually_pos] with U hU hgU
    apply ae_of_all
    intro s hs
    have hs' : 0 < s ∧ s ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      exact hs
    have hgs : 0 ≤ g (s * U) := hnonneg _
    have hle : g (s * U) ≤ g U := by
      apply hmono
      simpa using mul_le_mul_of_nonneg_right hs'.2 hU.le
    have hratio : 0 ≤ F U s ∧ F U s ≤ 1 := by
      dsimp [F]
      constructor
      · exact div_nonneg hgs hgU.le
      · exact (div_le_one hgU).2 hle
    rw [Real.norm_eq_abs, abs_of_nonneg hratio.1]
    exact hratio.2
  have hlim : ∀ᵐ s ∂volume,
      s ∈ Ι (0:ℝ) 1 → Tendsto (fun U : ℝ => F U s) atTop (nhds (s ^ ρ)) := by
    apply ae_of_all
    intro s hs
    have hs' : 0 < s ∧ s ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      exact hs
    change Tendsto (fun U : ℝ => g (s * U) / g U) atTop (nhds (s ^ ρ))
    exact hreg.ratio_tendsto hs'.1
  have hdom : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (0:ℝ)) (b := 1)
      (F := F) (f := fun s => s ^ ρ) (bound := fun _ => (1:ℝ))
      hFmeas hbound hdom hlim
  have hpower : (∫ s in (0:ℝ)..1, s ^ ρ) = 1 / (ρ + 1) := by
    rw [integral_rpow (Or.inl hρ)]
    simp [Real.zero_rpow, ne_of_gt (by linarith : 0 < ρ + 1)]
  rw [hpower] at hDCT
  have hchange (U : ℝ) (hU : 0 < U) :
      (∫ s in (0:ℝ)..1, F U s) =
        (∫ t in (0:ℝ)..U, g t) / (U * g U) := by
    have hcomp := intervalIntegral.integral_comp_mul_right (f := g)
      (a := (0:ℝ)) (b := 1) (c := U) hU.ne'
    have hfunc : (fun s : ℝ => g (s * U) / g U) =
        fun s => g (s * U) * (g U)⁻¹ := by
      ext s
      rw [div_eq_mul_inv]
    dsimp [F]
    rw [hfunc, intervalIntegral.integral_mul_const, hcomp]
    simp only [zero_mul, one_mul, smul_eq_mul]
    field_simp [ne_of_gt hU]
  have heq : (fun U : ℝ =>
      (∫ t in (0:ℝ)..U, g t) / (U * g U)) =ᶠ[atTop]
      fun U => ∫ s in (0:ℝ)..1, F U s := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
    exact (hchange U hU).symm
  exact hDCT.congr' heq.symm

/-- Karamata's integral theorem for a bounded antitone regularly varying
function. If `g` has index `-β`, `0 ≤ β < 1`, and is eventually positive, then
`∫₀ᵁ g(t) dt` is asymptotic to `U * g(U) / (1 - β)`. -/
theorem IsRegularlyVaryingAtTop.tendsto_intervalIntegral_div_mul_of_antitone
    {g : ℝ → ℝ} {β : ℝ}
    (hreg : IsRegularlyVaryingAtTop g (-β))
    (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (hanti : Antitone g)
    (hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t)
    (hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1) :
    Tendsto (fun U : ℝ =>
      (∫ t in (0:ℝ)..U, g t) / (U * g U)) atTop
      (nhds (1 / (1 - β))) := by
  let ε : ℝ := (1 - β) / 2
  let p : ℝ := β + ε
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hp0 : 0 ≤ p := by dsimp [p, ε]; linarith
  have hp1 : p < 1 := by dsimp [p, ε]; linarith
  have hpowIntegrable (q : ℝ) (hq : -1 < q) :
      IntervalIntegrable (fun s : ℝ => s ^ q) volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_rpow' hq
  let f : ℝ → ℝ := fun x => (g x)⁻¹
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < g x := hreg.eventually_pos
  obtain ⟨Rpos, hRpos⟩ := eventually_atTop.1 hpos
  have hfmono : IsEventuallyMonotoneAtTop f := by
    refine ⟨Rpos, ?_⟩
    intro x y hx hxy
    have hgx : 0 < g x := hRpos x hx
    have hgy : 0 < g y := hRpos y (le_trans hx hxy)
    dsimp [f]
    simpa [one_div] using one_div_le_one_div_of_le hgy (hanti hxy)
  have hfreg : IsRegularlyVaryingAtTop f β := by
    simpa [f] using hreg.inv
  obtain ⟨Rpot, hRpot, hpot⟩ :=
    hfreg.exists_potter_upper_bound hfmono hβ₀ hε
  let R : ℝ := max 1 (max Rpos Rpot)
  have hRpos' : 0 < R := by dsimp [R]; positivity
  have hRposLe : Rpos ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_left _ _)
  have hRpotLe : Rpot ≤ R := by
    dsimp [R]
    exact le_trans (le_max_right Rpos Rpot) (le_max_right 1 (max Rpos Rpot))
  have hpositive : ∀ ⦃x : ℝ⦄, R ≤ x → 0 < g x := by
    intro x hx
    exact hRpos x (le_trans hRposLe hx)
  have hpotter : ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y →
      f y / f x ≤ 2 ^ p * (y / x) ^ p := by
    intro x y hx hxy
    exact hpot (le_trans hRpotLe hx) hxy
  have hbase : 0 < g R := hpositive le_rfl
  have hrecipBound : ∀ ⦃U : ℝ⦄, R ≤ U →
      (g U)⁻¹ ≤ (2 ^ p / g R) * (U / R) ^ p := by
    intro U hU
    have h := hpotter (x := R) (y := U) le_rfl hU
    dsimp [f] at h
    have hUpos : 0 < g U := hpositive hU
    have hmul : g R * (g U)⁻¹ ≤ 2 ^ p * (U / R) ^ p := by
      simpa [f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hquot : (g U)⁻¹ ≤ (2 ^ p * (U / R) ^ p) / g R :=
      (le_div_iff₀ hbase).2 (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hquot
  let F : ℝ → ℝ → ℝ := fun U s => g (s * U) / g U
  have hg_meas : Measurable g := hanti.measurable
  have hF_meas : ∀ᶠ U : ℝ in atTop, AEStronglyMeasurable (F U)
      (volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [] with U
    have hmeas : Measurable (F U) := by
      dsimp [F]
      exact (hg_meas.comp (measurable_id.mul_const U)).div measurable_const
    exact hmeas.aestronglyMeasurable
  have hbound : ∀ᶠ U : ℝ in atTop, ∀ᵐ s ∂volume,
      s ∈ Ι (0:ℝ) 1 → ‖F U s‖ ≤ (2 ^ p / g R) * s ^ (-p) := by
    filter_upwards [eventually_ge_atTop R] with U hU
    apply ae_of_all
    intro s hs
    have hs' : 0 < s ∧ s ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      exact hs
    have hspos : 0 < s := hs'.1
    have hUpos : 0 < U := lt_of_lt_of_le hRpos' hU
    have hgU : 0 < g U := hpositive hU
    have hgs_nonneg : 0 ≤ g (s * U) := hg_nonneg (mul_nonneg hs'.1.le hUpos.le)
    have hratio_nonneg : 0 ≤ g (s * U) / g U := div_nonneg hgs_nonneg hgU.le
    rw [Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
    by_cases hlarge : R ≤ s * U
    · have hgs : 0 < g (s * U) := hpositive hlarge
      have hpot := hpotter (x := s * U) (y := U) hlarge (by nlinarith [hs'.2, hU])
      have hratio : g (s * U) / g U ≤ 2 ^ p * s ^ (-p) := by
        have hpot' : g (s * U) / g U ≤ 2 ^ p * (U / (s * U)) ^ p := by
          convert hpot using 1
          · dsimp [f]
            field_simp [ne_of_gt hgs, ne_of_gt hgU]
        have harg : U / (s * U) = s⁻¹ := by field_simp [ne_of_gt hspos, ne_of_gt hUpos]
        rw [harg, ← Real.rpow_neg_eq_inv_rpow] at hpot'
        exact hpot'
      calc
        g (s * U) / g U ≤ 2 ^ p * s ^ (-p) := hratio
        _ ≤ (2 ^ p / g R) * s ^ (-p) := by
          have hRle1 : g R ≤ 1 := hg_le_one hRpos'.le
          have hone : (1:ℝ) ≤ (g R)⁻¹ := by
            simpa [one_div] using one_div_le_one_div_of_le hbase hRle1
          calc
            2 ^ p * s ^ (-p) = 2 ^ p * 1 * s ^ (-p) := by ring
            _ ≤ 2 ^ p * (g R)⁻¹ * s ^ (-p) := by gcongr
            _ = (2 ^ p / g R) * s ^ (-p) := by ring
    · have hUs : s * U < R := lt_of_not_ge hlarge
      have hbaseBound := hrecipBound hU
      have hscaled : U / R ≤ s⁻¹ := by
        apply (div_le_iff₀ hRpos').2
        have hdiv : U < R / s := (lt_div_iff₀ hspos).2 (by simpa [mul_comm] using hUs)
        simpa [div_eq_mul_inv, mul_comm] using hdiv.le
      have hscaledPow : (U / R) ^ p ≤ (s⁻¹) ^ p :=
        Real.rpow_le_rpow (by positivity) hscaled hp0
      have hratio : g (s * U) / g U ≤ (2 ^ p / g R) * s ^ (-p) := by
        have hleft : g (s * U) / g U ≤ (g U)⁻¹ := by
          rw [div_le_iff₀ hgU]
          calc
            g (s * U) ≤ 1 := hg_le_one (mul_nonneg hspos.le hUpos.le)
            _ = (g U)⁻¹ * g U := by field_simp
        calc
          g (s * U) / g U ≤ (g U)⁻¹ := hleft
          _ ≤ (2 ^ p / g R) * (U / R) ^ p := hbaseBound
          _ ≤ (2 ^ p / g R) * (s⁻¹) ^ p :=
            mul_le_mul_of_nonneg_left hscaledPow (by positivity)
          _ = (2 ^ p / g R) * s ^ (-p) := by rw [← Real.rpow_neg_eq_inv_rpow]
      exact hratio
  have hlim : ∀ᵐ s ∂volume, s ∈ Ι (0:ℝ) 1 →
      Tendsto (fun U : ℝ => F U s) atTop (𝓝 (s ^ (-β))) := by
    apply ae_of_all
    intro s hs
    have hs' : 0 < s ∧ s ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      exact hs
    change Tendsto (fun U : ℝ => g (s * U) / g U) atTop (𝓝 (s ^ (-β)))
    exact hreg.ratio_tendsto (c := s) hs'.1
  have hdomInt : IntervalIntegrable (fun s : ℝ => (2 ^ p / g R) * s ^ (-p))
      volume 0 1 := by
    simpa only [mul_comm] using (hpowIntegrable (-p) (by linarith : -1 < -p)).const_mul
      (2 ^ p / g R)
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (0:ℝ)) (b := 1)
      (F := F) (f := fun s => s ^ (-β))
      (fun s => (2 ^ p / g R) * s ^ (-p)) hF_meas hbound hdomInt hlim
  have hlimitIntegral : Tendsto
      (fun U : ℝ => ∫ s in (0:ℝ)..1, F U s) atTop
      (nhds (∫ s in (0:ℝ)..1, s ^ (-β))) := hDCT
  have hpowIntegral : (∫ s in (0:ℝ)..1, s ^ (-β)) = 1 / (1 - β) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -β))]
    rw [show -β + 1 = 1 - β by ring]
    simp [Real.zero_rpow, ne_of_gt (by linarith : 0 < 1 - β)]
  rw [hpowIntegral] at hlimitIntegral
  have hchange (U : ℝ) (hU : 0 < U) :
      (∫ s in (0:ℝ)..1, F U s) =
        (∫ t in (0:ℝ)..U, g t) / (U * g U) := by
    have hcomp := intervalIntegral.integral_comp_mul_right (f := g) (a := (0:ℝ))
      (b := 1) (c := U) hU.ne'
    dsimp [F]
    have hfunc : (fun s : ℝ => g (s * U) / g U) =
        fun s => (g (s * U)) * (g U)⁻¹ := by
      ext s
      rw [div_eq_mul_inv]
    rw [hfunc, intervalIntegral.integral_mul_const, hcomp]
    simp only [zero_mul, one_mul, smul_eq_mul]
    field_simp [ne_of_gt hU]
  have heq : (fun U : ℝ =>
      (∫ t in (0:ℝ)..U, g t) / (U * g U)) =ᶠ[atTop]
      fun U => ∫ s in (0:ℝ)..1, F U s := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
    exact (hchange U hU).symm
  exact hlimitIntegral.congr' heq.symm

end Asymptotics
