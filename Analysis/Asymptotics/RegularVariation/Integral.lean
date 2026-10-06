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
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integral asymptotics for regularly varying tails

This file proves the integral form of Karamata's theorem needed for truncated
moments. The proof uses a Potter bound and dominated convergence.
-/

open Filter MeasureTheory Set Topology
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

private theorem exists_pow_two_bracket (s : ℝ) (hs : 1 ≤ s) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ s ∧ s < (2 : ℝ) ^ (k + 1) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hex : ∃ n : ℕ, s < (2 : ℝ) ^ n :=
    (hpow.eventually (eventually_gt_atTop s)).exists
  let n₀ := Nat.find hex
  have hn₀ : s < (2 : ℝ) ^ n₀ := Nat.find_spec hex
  have hn₀pos : 0 < n₀ := by
    by_contra h
    have heq : n₀ = 0 := Nat.eq_zero_of_not_pos h
    rw [heq] at hn₀
    linarith
  have hn₀ne : n₀ ≠ 0 := Nat.ne_of_gt hn₀pos
  have hprev : ¬ s < (2 : ℝ) ^ n₀.pred := by
    intro hsmall
    have hmin := Nat.find_min' hex hsmall
    exact (not_le_of_gt (Nat.pred_lt hn₀ne)) hmin
  refine ⟨n₀.pred, le_of_not_gt hprev, ?_⟩
  have hnsucc : n₀.pred + 1 = n₀ := by
    simpa using Nat.succ_pred_eq_of_pos hn₀pos
  calc
    s < (2 : ℝ) ^ n₀ := hn₀
    _ = (2 : ℝ) ^ (n₀.pred + 1) := by rw [hnsucc]

/-- Karamata's upper-tail integral theorem for a nonnegative antitone
regularly varying function. For index `-β` with `β > 1`, the tail integral is
asymptotic to `x * g x / (β - 1)`. The domination uses a dyadic Potter bound;
the limit follows from Mathlib's dominated-convergence theorem. -/
theorem IsRegularlyVaryingAtTop.tendsto_integral_Ioi_div_mul_of_antitone
    {g : ℝ → ℝ} {β : ℝ}
    (hreg : IsRegularlyVaryingAtTop g (-β))
    (hβ : 1 < β)
    (hanti : Antitone g)
    (hgnonneg : ∀ x, 0 ≤ g x) :
    Tendsto (fun U : ℝ => (∫ t in Ioi U, g t) / (U * g U)) atTop
      (nhds (1 / (β - 1))) := by
  let p : ℝ := (β + 1) / 2
  let q : ℝ := (2 : ℝ) ^ (-p)
  have hpβ : p < β := by dsimp [p]; linarith
  have hp1 : 1 < p := by dsimp [p]; linarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq_lt : 2 ^ (-β) < q := by
    dsimp [q]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith)
  have hratioTwo := hreg.ratio_tendsto (c := 2) (by norm_num : (0 : ℝ) < 2)
  have hratioEvent : ∀ᶠ U : ℝ in atTop, g (2 * U) / g U < q :=
    hratioTwo.eventually (Iio_mem_nhds hq_lt)
  obtain ⟨Rratio, hRratio⟩ := eventually_atTop.1 hratioEvent
  obtain ⟨Rpositive, hRpositive⟩ := eventually_atTop.1 hreg.eventually_pos
  let R : ℝ := max 1 (max Rratio Rpositive)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRratioLe : Rratio ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_left _ _)
  have hRpositiveLe : Rpositive ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_right _ _)
  have hpositive : ∀ ⦃U : ℝ⦄, R ≤ U → 0 < g U := by
    intro U hU
    exact hRpositive U (le_trans hRpositiveLe hU)
  have hstep : ∀ ⦃U : ℝ⦄, R ≤ U → g (2 * U) ≤ q * g U := by
    intro U hU
    have hratio := hRratio U (le_trans hRratioLe hU)
    exact (div_lt_iff₀ (hpositive hU)).1 hratio |>.le
  have hiter : ∀ (k : ℕ) ⦃U : ℝ⦄, R ≤ U →
      g ((2 : ℝ) ^ k * U) ≤ q ^ k * g U := by
    intro k
    induction k with
    | zero =>
        intro U hU
        simp
    | succ k ih =>
        intro U hU
        have hpow : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hUpos : 0 < U := lt_of_lt_of_le hRpos hU
        have hbase : R ≤ (2 : ℝ) ^ k * U := by
          calc
            R ≤ U := hU
            _ ≤ (2 : ℝ) ^ k * U := by
              simpa using mul_le_mul_of_nonneg_right hpow hUpos.le
        have hstep' := hstep hbase
        have hmul : q * g ((2 : ℝ) ^ k * U) ≤ q * (q ^ k * g U) :=
          mul_le_mul_of_nonneg_left (ih hU) hqpos.le
        calc
          g ((2 : ℝ) ^ (k + 1) * U) = g (2 * ((2 : ℝ) ^ k * U)) := by
            congr 1
            rw [pow_succ]
            ring
          _ ≤ q * g ((2 : ℝ) ^ k * U) := hstep'
          _ ≤ q * (q ^ k * g U) := hmul
          _ = q ^ (k + 1) * g U := by rw [pow_succ]; ring
  let F : ℝ → ℝ → ℝ := fun U s => g (s * U) / g U
  have hgmeas : Measurable g := hanti.measurable
  have hFmeas : ∀ᶠ U : ℝ in atTop,
      AEStronglyMeasurable (F U) (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards [] with U
    have hmeas : Measurable (F U) := by
      dsimp [F]
      exact (hgmeas.comp (measurable_id.mul_const U)).div measurable_const
    exact hmeas.aestronglyMeasurable
  have hbound : ∀ᶠ U : ℝ in atTop, ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
      ‖F U s‖ ≤ 2 ^ p * s ^ (-p) := by
    filter_upwards [eventually_ge_atTop R] with U hU
    have hUpos : 0 < U := lt_of_lt_of_le hRpos hU
    have hgU : 0 < g U := hpositive hU
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsone : 1 ≤ s := le_of_lt hs
    have hspos : 0 < s := lt_trans zero_lt_one hs
    have hgsnonneg : 0 ≤ g (s * U) := hgnonneg _
    have hFnonneg : 0 ≤ F U s := by
      dsimp [F]
      exact div_nonneg hgsnonneg hgU.le
    rw [Real.norm_eq_abs, abs_of_nonneg hFnonneg]
    obtain ⟨k, hklo, hkup⟩ := exists_pow_two_bracket s hsone
    have hscale : (2 : ℝ) ^ k * U ≤ s * U :=
      mul_le_mul_of_nonneg_right hklo hUpos.le
    have hmono := hanti hscale
    have hiter' := hiter k hU
    have hratio : g (s * U) / g U ≤ q ^ k := by
      calc
        g (s * U) / g U ≤ g ((2 : ℝ) ^ k * U) / g U :=
          div_le_div_of_nonneg_right hmono hgU.le
        _ ≤ (q ^ k * g U) / g U :=
          div_le_div_of_nonneg_right hiter' hgU.le
        _ = q ^ k := by field_simp
    have hqpow : q ^ k = ((2 : ℝ) ^ k) ^ (-p) := by
      calc
        q ^ k = ((2 : ℝ) ^ (-p)) ^ k := rfl
        _ = (2 : ℝ) ^ ((-p) * (k : ℝ)) := by
          rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (2 : ℝ) ^ ((k : ℝ) * (-p)) := by
          congr 1
          ring
        _ = ((2 : ℝ) ^ k) ^ (-p) := by
          rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpowle : ((2 : ℝ) ^ (k + 1)) ^ (-p) ≤ s ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hspos
        (le_of_lt hkup) (by linarith)
    have htwo : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    have hpowFactor : q ^ k = 2 ^ p * ((2 : ℝ) ^ (k + 1)) ^ (-p) := by
      rw [hqpow, htwo, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ (2 : ℝ) ^ k)]
      have hmul : (2 : ℝ) ^ p * (2 : ℝ) ^ (-p) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        simp
      rw [← mul_assoc, hmul, one_mul]
    calc
      F U s ≤ q ^ k := by simpa [F] using hratio
      _ = 2 ^ p * ((2 : ℝ) ^ (k + 1)) ^ (-p) := hpowFactor
      _ ≤ 2 ^ p * s ^ (-p) := mul_le_mul_of_nonneg_left hpowle (by positivity)
  have hlim : ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun U : ℝ => F U s) atTop (nhds (s ^ (-β))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := lt_trans zero_lt_one hs
    change Tendsto (fun U : ℝ => g (s * U) / g U) atTop (nhds (s ^ (-β)))
    exact hreg.ratio_tendsto hspos
  have hdom : Integrable (fun s : ℝ => 2 ^ p * s ^ (-p))
      (volume.restrict (Ioi (1 : ℝ))) := by
    have hrpow : IntegrableOn (fun s : ℝ => s ^ (-p)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith [hp1] : -p < -1) (by norm_num)
    simpa [IntegrableOn] using hrpow.const_mul (2 ^ p)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun U s => F U s) (f := fun s => s ^ (-β))
    (bound := fun s => 2 ^ p * s ^ (-p)) hFmeas hbound hdom hlim
  have hlimitIntegral : Tendsto
      (fun U : ℝ => ∫ s in Ioi (1 : ℝ), F U s) atTop
      (nhds (∫ s in Ioi (1 : ℝ), s ^ (-β))) := hDCT
  have hpowIntegral : (∫ s in Ioi (1 : ℝ), s ^ (-β)) = 1 / (β - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith [hβ]) (by norm_num)]
    simp only [Real.one_rpow]
    have hne : β - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [show -β + 1 = -(β - 1) by ring]
    field_simp [hne]
  rw [hpowIntegral] at hlimitIntegral
  have hchange (U : ℝ) (hU : R ≤ U) :
      (∫ s in Ioi (1 : ℝ), F U s) =
        (∫ t in Ioi U, g t) / (U * g U) := by
    have hUpos : 0 < U := lt_of_lt_of_le hRpos hU
    have hgU : 0 < g U := hpositive hU
    have hfun : (fun s : ℝ => F U s) =
        fun s => (g U)⁻¹ * g (s * U) := by
      funext s
      simp [F, div_eq_mul_inv, mul_comm]
    calc
      (∫ s in Ioi (1 : ℝ), F U s) =
          (g U)⁻¹ * ∫ s in Ioi (1 : ℝ), g (s * U) := by
            rw [hfun]
            exact integral_const_mul _ _
      _ = (g U)⁻¹ * (U⁻¹ * ∫ t in Ioi U, g t) := by
            rw [integral_comp_mul_right_Ioi g 1 hUpos]
            simp only [one_mul, smul_eq_mul]
      _ = (∫ t in Ioi U, g t) / (U * g U) := by
            field_simp [ne_of_gt hUpos, ne_of_gt hgU]
  have heq : (fun U : ℝ => (∫ s in Ioi (1 : ℝ), F U s)) =ᶠ[atTop]
      fun U => (∫ t in Ioi U, g t) / (U * g U) := by
    filter_upwards [eventually_ge_atTop R] with U hU
    exact hchange U hU
  exact hlimitIntegral.congr' heq

end Asymptotics
