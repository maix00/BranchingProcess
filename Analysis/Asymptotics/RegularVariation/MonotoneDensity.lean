/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Monotone density for regularly varying primitives

If a positive antitone function has a regularly varying primitive with positive
index, then the density is regularly varying with index one less. This is the
monotone-density step used when recovering a tail from an integrated tail.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace Asymptotics

private theorem rpow_slope_right_one (ρ : ℝ) :
    Tendsto (fun δ : ℝ => ((1 + δ) ^ ρ - 1) / δ)
      (𝓝[>] (0 : ℝ)) (nhds ρ) := by
  have hderiv : HasDerivAt (fun x : ℝ => x ^ ρ) ρ 1 := by
    convert Real.hasDerivAt_rpow_const (p := ρ) (Or.inl one_ne_zero) using 1
    simp
  have h := hderiv.tendsto_slope_zero_right
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- A monotone density is regularly varying when its interval primitive is.
The local integrability assumption makes the primitive a genuine interval
integral; the proof squeezes its density between two difference quotients and
then lets their fixed multiplier decrease to one. -/
theorem IsRegularlyVaryingAtTop.of_monotone_intervalIntegral
    {g : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hmono : Monotone g ∨ Antitone g)
    (hpos : ∀ᶠ x : ℝ in atTop, 0 < g x)
    (hint : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hF : IsRegularlyVaryingAtTop
      (fun x : ℝ => ∫ t in (0:ℝ)..x, g t) ρ) :
    IsRegularlyVaryingAtTop g (ρ - 1) := by
  let F : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t
  let Q : ℝ → ℝ := fun x => x * g x / F x
  have hFpos : ∀ᶠ x : ℝ in atTop, 0 < F x := hF.eventually_pos

  have hQ : Tendsto Q atTop (nhds ρ) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hε4 : 0 < ε / 4 := by positivity
    let A : ℝ → ℝ := fun δ => ((1 + δ) ^ ρ - 1) / δ
    let B : ℝ → ℝ := fun δ => A δ * (1 + δ) ^ (1 - ρ)
    have hA : Tendsto A (𝓝[>] (0:ℝ)) (nhds ρ) := by
      simpa [A] using rpow_slope_right_one ρ
    have hpowArg : Tendsto (fun δ : ℝ => 1 + δ) (𝓝[>] (0:ℝ)) (nhds 1) := by
      have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (0:ℝ)) (nhds 1) :=
        tendsto_const_nhds
      have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hconst.add hid
    have hpowCont : ContinuousAt (fun x : ℝ => x ^ (1 - ρ)) 1 :=
      Real.continuousAt_rpow_const 1 (1 - ρ) (Or.inl one_ne_zero)
    have hpow : Tendsto (fun δ : ℝ => (1 + δ) ^ (1 - ρ))
        (𝓝[>] (0:ℝ)) (nhds 1) := by
      have h := hpowCont.tendsto.comp hpowArg
      simpa [Function.comp_def] using h
    have hB : Tendsto B (𝓝[>] (0:ℝ)) (nhds ρ) := by
      simpa [B] using hA.mul hpow
    have hAevent : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), |A δ - ρ| < ε / 4 := by
      have h := hA.eventually (Metric.ball_mem_nhds ρ hε4)
      filter_upwards [h] with δ hδ
      simpa [Real.dist_eq] using hδ
    have hBevent : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), |B δ - ρ| < ε / 4 := by
      have h := hB.eventually (Metric.ball_mem_nhds ρ hε4)
      filter_upwards [h] with δ hδ
      simpa [Real.dist_eq] using hδ
    obtain ⟨δ, ⟨hδA, hδB⟩, hδpos⟩ :=
      ((hAevent.and hBevent).and self_mem_nhdsWithin).exists
    let c : ℝ := 1 + δ
    have hc : 1 < c := by dsimp [c]; linarith
    have hcpos : 0 < c := by linarith
    have hcinvpos : 0 < c⁻¹ := inv_pos.mpr hcpos
    have hdenL : 0 < c - 1 := by linarith
    have hdenU : 0 < 1 - c⁻¹ := by
      apply sub_pos.mpr
      exact (inv_lt_one₀ hcpos).2 hc

    let L : ℝ → ℝ := fun x => (F (c * x) / F x - 1) / (c - 1)
    let U : ℝ → ℝ := fun x => (1 - F (x / c) / F x) / (1 - c⁻¹)
    have hLlim : Tendsto L atTop
        (nhds ((c ^ ρ - 1) / (c - 1))) := by
      have hratio := hF.ratio_tendsto (c := c) hcpos
      have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have hsub := hratio.sub hconst
      simpa [L, F] using hsub.div_const (c - 1)
    have hUlim : Tendsto U atTop
        (nhds ((1 - c ^ (-ρ)) / (1 - c⁻¹))) := by
      have hratio := hF.ratio_tendsto (c := c⁻¹) hcinvpos
      have hratio' : Tendsto (fun x : ℝ => F (x / c) / F x) atTop
          (nhds (c⁻¹ ^ ρ)) := by
        have heq : (fun x : ℝ => F (c⁻¹ * x) / F x) =ᶠ[atTop]
            fun x => F (x / c) / F x := by
          filter_upwards [] with x
          simp [div_eq_mul_inv, mul_comm]
        simpa [one_div] using hratio.congr' heq
      have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have hsub := hconst.sub hratio'
      have hdiv := hsub.div_const (1 - c⁻¹)
      have hpow : c⁻¹ ^ ρ = c ^ (-ρ) := by
        rw [← Real.rpow_neg_eq_inv_rpow c ρ]
      simpa [U, F, hpow] using hdiv

    have hlimitL : |((c ^ ρ - 1) / (c - 1)) - ρ| < ε / 4 := by
      simpa [A, c] using hδA
    have hlimitU : |((1 - c ^ (-ρ)) / (1 - c⁻¹)) - ρ| < ε / 4 := by
      have hidentity : (1 - c ^ (-ρ)) / (1 - c⁻¹) = B δ := by
        dsimp [B, A, c]
        have hrpowNeg : (1 + δ) ^ (-ρ) = ((1 + δ) ^ ρ)⁻¹ :=
          Real.rpow_neg (by linarith : 0 ≤ 1 + δ) ρ
        rw [hrpowNeg]
        have hpowSub : (1 + δ) ^ (1 - ρ) =
            (1 + δ) / (1 + δ) ^ ρ := by
          rw [Real.rpow_sub (by linarith : 0 < 1 + δ), Real.rpow_one]
        rw [hpowSub]
        field_simp [ne_of_gt hδpos, ne_of_gt (by linarith : 0 < 1 + δ)]
        ring
      rw [hidentity]
      exact hδB

    have hLclose : ∀ᶠ x : ℝ in atTop, |L x - ((c ^ ρ - 1) / (c - 1))| < ε / 4 := by
      exact hLlim.eventually (Metric.ball_mem_nhds _ hε4) |>.mono fun x hx => by
        simpa [Real.dist_eq] using hx
    have hUclose : ∀ᶠ x : ℝ in atTop,
        |U x - ((1 - c ^ (-ρ)) / (1 - c⁻¹))| < ε / 4 := by
      exact hUlim.eventually (Metric.ball_mem_nhds _ hε4) |>.mono fun x hx => by
        simpa [Real.dist_eq] using hx

    have hQbounds : ∀ᶠ x : ℝ in atTop,
        (L x ≤ Q x ∧ Q x ≤ U x) ∨ (U x ≤ Q x ∧ Q x ≤ L x) := by
      filter_upwards [eventually_gt_atTop (0:ℝ), hFpos, hpos,
        eventually_gt_atTop (0:ℝ)] with x hx hFx hgx hx'
      have hFxInt : F (c * x) = F x + ∫ t in x..(c * x), g t := by
        dsimp [F]
        symm
        exact intervalIntegral.integral_add_adjacent_intervals (hint 0 x) (hint x (c*x))
      have hprevInt : F x = F (x / c) + ∫ t in (x / c)..x, g t := by
        dsimp [F]
        symm
        exact intervalIntegral.integral_add_adjacent_intervals (hint 0 (x/c)) (hint (x/c) x)
      have habPlus : x ≤ c*x := by nlinarith [hc, hx]
      have habMinus : x/c ≤ x :=
        (div_le_iff₀ hcpos).2 (by nlinarith [hc, hx])
      have hratioL : F (c*x) / F x - 1 = (F (c*x) - F x) / F x := by
        field_simp
      have hratioU : 1 - F (x/c) / F x = (F x - F (x/c)) / F x := by
        field_simp
      rcases hmono with hmon | hanti
      · have hplusLower : (c*x-x) * g x ≤ ∫ t in x..(c*x), g t := by
          have hmonoInt := intervalIntegral.integral_mono_on habPlus
            intervalIntegrable_const (hint x (c*x)) (fun t ht => hmon ht.1)
          simpa [intervalIntegral.integral_const, smul_eq_mul] using hmonoInt
        have hminusUpper : ∫ t in (x/c)..x, g t ≤ (x-x/c) * g x := by
          have hmonoInt := intervalIntegral.integral_mono_on habMinus
            (hint (x/c) x) intervalIntegrable_const (fun t ht => hmon ht.2)
          simpa [intervalIntegral.integral_const, smul_eq_mul] using hmonoInt
        have hLnum : (c-1)*x*g x ≤ F (c*x) - F x := by
          rw [hFxInt]
          have hmul : (c*x-x) * g x = (c-1)*x*g x := by ring
          nlinarith [hplusLower]
        have hUnum : F x - F (x/c) ≤ (1-c⁻¹)*x*g x := by
          rw [hprevInt]
          have hmul : (x-x/c)*g x = (1-c⁻¹)*x*g x := by
            field_simp [ne_of_gt hcpos]
          nlinarith [hminusUpper]
        have hLbound : Q x ≤ L x := by
          dsimp [L, Q]
          rw [hratioL]
          have heq : (F (c*x) - F x) / F x / (c-1) =
              (F (c*x) - F x) / (F x * (c-1)) := by
            field_simp [ne_of_gt hFx, ne_of_gt hdenL]
          rw [heq]
          apply (div_le_div_iff₀ hFx (mul_pos hFx hdenL)).2
          nlinarith [mul_le_mul_of_nonneg_right hLnum hFx.le]
        have hUbound : U x ≤ Q x := by
          dsimp [U, Q]
          rw [hratioU]
          have heq : (F x - F (x/c)) / F x / (1-c⁻¹) =
              (F x - F (x/c)) / (F x * (1-c⁻¹)) := by
            field_simp [ne_of_gt hFx, ne_of_gt hdenU]
          rw [heq]
          apply (div_le_div_iff₀ (mul_pos hFx hdenU) hFx).2
          nlinarith [mul_le_mul_of_nonneg_right hUnum hFx.le]
        exact Or.inr ⟨hUbound, hLbound⟩
      · have hplusUpper : ∫ t in x..(c*x), g t ≤ (c*x-x) * g x := by
          have hmonoInt := intervalIntegral.integral_mono_on habPlus
            (hint x (c*x)) intervalIntegrable_const (fun t ht => hanti ht.1)
          simpa [intervalIntegral.integral_const, smul_eq_mul] using hmonoInt
        have hminusLower : (x-x/c) * g x ≤ ∫ t in (x/c)..x, g t := by
          have hmonoInt := intervalIntegral.integral_mono_on habMinus
            intervalIntegrable_const (hint (x/c) x) (fun t ht => hanti ht.2)
          simpa [intervalIntegral.integral_const, smul_eq_mul] using hmonoInt
        have hLnum : F (c*x) - F x ≤ (c-1)*x*g x := by
          rw [hFxInt]
          have hmul : (c*x-x) * g x = (c-1)*x*g x := by ring
          nlinarith [hplusUpper]
        have hUnum : (1-c⁻¹)*x*g x ≤ F x - F (x/c) := by
          rw [hprevInt]
          have hmul : (x-x/c)*g x = (1-c⁻¹)*x*g x := by
            field_simp [ne_of_gt hcpos]
          nlinarith [hminusLower]
        have hLbound : L x ≤ Q x := by
          dsimp [L, Q]
          rw [hratioL]
          apply (div_le_iff₀ hdenL).2
          apply (div_le_iff₀ hFx).2
          have heq : x * g x / F x * (c-1) * F x = (c-1)*x*g x := by
            field_simp [ne_of_gt hFx]
          rw [heq]
          exact hLnum
        have hUbound : Q x ≤ U x := by
          dsimp [U, Q]
          rw [hratioU]
          apply (div_le_iff₀ hFx).2
          have heq : (F x - F (x/c)) / F x / (1-c⁻¹) * F x =
              (F x - F (x/c)) / (1-c⁻¹) := by
            field_simp [ne_of_gt hFx, ne_of_gt hdenU]
          rw [heq]
          apply (le_div_iff₀ hdenU).2
          nlinarith [hUnum]
        exact Or.inl ⟨hLbound, hUbound⟩

    filter_upwards [hQbounds, hLclose, hUclose] with x hx hLx hUx
    have hLlower : ρ - ε / 2 < L x := by
      have hclose := abs_lt.mp hLx
      have hlimit := abs_lt.mp hlimitL
      linarith
    have hUlower : ρ - ε / 2 < U x := by
      have hclose := abs_lt.mp hUx
      have hlimit := abs_lt.mp hlimitU
      linarith
    have hLupper : L x < ρ + ε / 2 := by
      have hclose := abs_lt.mp hLx
      have hlimit := abs_lt.mp hlimitL
      linarith
    have hUupper : U x < ρ + ε / 2 := by
      have hclose := abs_lt.mp hUx
      have hlimit := abs_lt.mp hlimitU
      linarith
    have hQlower : ρ - ε < Q x := by
      rcases hx with ⟨hLQ, _⟩ | ⟨hUQ, _⟩ <;> linarith
    have hQupper : Q x < ρ + ε := by
      rcases hx with ⟨_, hQU⟩ | ⟨_, hQL⟩ <;> linarith
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith

  refine ⟨hpos, ?_⟩
  · intro c hc
    have hcTop : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hQnum : Tendsto (fun x : ℝ => Q (c*x)) atTop (nhds ρ) := hQ.comp hcTop
    have hQden : Tendsto Q atTop (nhds ρ) := hQ
    have hQratio : Tendsto (fun x : ℝ => Q (c*x) / Q x) atTop (nhds 1) := by
      have h := hQnum.div hQden hρ.ne'
      convert h using 1
      · simp [hρ.ne']
    have hFratio := hF.ratio_tendsto hc
    have hFpos' : ∀ᶠ x : ℝ in atTop, 0 < F x := hFpos
    have hgpos' : ∀ᶠ x : ℝ in atTop, 0 < g x := hpos
    have hratioEq : (fun x : ℝ => g (c*x) / g x) =ᶠ[atTop]
        fun x => (Q (c*x) / Q x) * (F (c*x) / F x) / c := by
      filter_upwards [eventually_gt_atTop (0:ℝ), hFpos', hgpos',
        hcTop.eventually hFpos, hcTop.eventually hpos] with x hx hFx hgx hFcx hgcx
      dsimp [Q]
      field_simp [ne_of_gt hx, ne_of_gt hFx, ne_of_gt hFcx,
        ne_of_gt hgx, ne_of_gt hgcx]
    have hlim := (hQratio.mul hFratio).div_const c
    have hpow : 1 * c ^ ρ / c = c ^ (ρ - 1) := by
      rw [one_mul, Real.rpow_sub hc ρ 1, Real.rpow_one]
    rw [hpow] at hlim
    exact hlim.congr' hratioEq.symm

end Asymptotics

end
