/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Sequence.LogarithmicScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Limits for natural-valued spans at a cubic scale

## Public declarations

* `Asymptotics.tendsto_natSpan_cubicRatio_of_stageRatios` gives
  $D_n/L_n^3\to t$ from $H_n/L_n^3\to t$ and $\ell_n/L_n^3\to0$.
* `Asymptotics.tendsto_natSpan_atTop_of_cubicRatio` gives $D_n\to\infty$.
* `Asymptotics.tendsto_natSpan_cubeRoot_div_scale` gives $D_n^{1/3}/L_n\to t^{1/3}$.
* `Asymptotics.tendsto_natSpan_sublinearPower_div_scale` gives
  $D_n^{p/3}/L_n\to0$ for $p<1$.

Here $L_n\to\infty$ is an arbitrary real scale and $t>0$.
The application $D_n=H_n-\ell_n$, $L_n=\log N_n$ occurs in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1, case $0<a<1$.
-/

open Filter
open scoped Topology

@[expose] public section

namespace Asymptotics

/-- A positive cubic-scale limit forces the planned span itself to diverge. -/
lemma tendsto_natSpan_atTop_of_cubicRatio
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t) :
    Tendsto (fun n => (D n : ℝ)) atTop atTop := by
  have hcube : Tendsto (fun n => L n ^ 3) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) |>.comp hL
  have hproduct := hcube.atTop_mul_pos ht hscale
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have heq : (fun n => L n ^ 3 * ((D n : ℝ) / L n ^ 3)) =ᶠ[atTop]
      fun n => (D n : ℝ) := by
    filter_upwards [hLpos] with n hn
    field_simp
  exact hproduct.congr' heq

/-- The cubic ratio of a two-stage span is the difference of the stage ratios,
provided the natural-valued cutoffs are eventually ordered. -/
lemma tendsto_natSpan_cubicRatio_of_stageRatios
    {ell ellN : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hEll : Tendsto (fun n => (ell n : ℝ) / L n ^ 3) atTop (𝓝 0))
    (hEllN : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (hellN : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n) :
    Tendsto (fun n => ((ellN n - ell n : ℕ) : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have heq :
      (fun n => ((ellN n - ell n : ℕ) : ℝ) / L n ^ 3) =ᶠ[atTop]
        fun n => (ellN n : ℝ) / L n ^ 3 - (ell n : ℝ) / L n ^ 3 := by
    filter_upwards [hellN, hLpos] with n horder hLn
    rw [Nat.cast_sub horder]
    field_simp
  simpa using (hEllN.sub hEll).congr' heq.symm

/-- A positive cubic-scale span has its cube-root width at the corresponding
linear logarithmic scale. -/
lemma tendsto_natSpan_cubeRoot_div_scale
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t)) (ht : 0 < t) :
    Tendsto (fun n => (D n : ℝ) ^ (3⁻¹ : ℝ) / L n)
      atTop (𝓝 (t ^ (3⁻¹ : ℝ))) := by
  have hpow :=
    (Real.continuousAt_rpow_const t (3⁻¹ : ℝ)
      (Or.inl (ne_of_gt ht))).tendsto.comp hscale
  have heq : (fun n => (D n : ℝ) ^ (3⁻¹ : ℝ) / L n) =ᶠ[atTop]
      fun n => ((D n : ℝ) / L n ^ 3) ^ (3⁻¹ : ℝ) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hLn
    have hden : ((L n : ℝ) ^ 3) ^ (3⁻¹ : ℝ) = L n := by
      rw [← Real.rpow_natCast (L n) 3, ← Real.rpow_mul hLn.le]
      have hexp : (↑(3 : ℕ) : ℝ) * (3⁻¹ : ℝ) = 1 := by norm_num
      rw [hexp, Real.rpow_one]
    rw [Real.div_rpow (Nat.cast_nonneg (D n)) (by positivity) (3⁻¹ : ℝ), hden]
  exact hpow.congr' heq.symm

/-- A power below one third of a cubic-scale natural span is negligible
relative to its real scale. The capacity application uses $p=1/2$. -/
lemma tendsto_natSpan_sublinearPower_div_scale
    {D : ℕ → ℕ} {L : ℕ → ℝ} {t p : ℝ}
    (hL : Tendsto L atTop atTop)
    (hscale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t)) (ht : 0 < t)
    (hp1 : p < 1) :
    Tendsto (fun n => (D n : ℝ) ^ (p / 3) / L n)
      atTop (𝓝 0) := by
  let q : ℝ := p / 3
  have hratio :=
    (Real.continuousAt_rpow_const t q (Or.inl (ne_of_gt ht))).tendsto.comp hscale
  have hLp : Tendsto (fun n => L n ^ (p - 1)) atTop (𝓝 0) := by
    have hneg := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).comp hL
    convert hneg using 1
    ext n
    congr 1
    ring
  have hprod := hratio.mul hLp
  have heq : (fun n => (D n : ℝ) ^ q / L n) =ᶠ[atTop]
      fun n => ((D n : ℝ) / L n ^ 3) ^ q * L n ^ (p - 1) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hLn
    have hDnonneg : 0 ≤ (D n : ℝ) := Nat.cast_nonneg _
    have hratioNonneg : 0 ≤ (D n : ℝ) / L n ^ 3 :=
      div_nonneg hDnonneg (by positivity)
    let r : ℝ := (D n : ℝ) / L n ^ 3
    have hr : r = (D n : ℝ) / L n ^ 3 := rfl
    have hfactor : (D n : ℝ) ^ q = r ^ q * L n ^ p := by
      have hsplit : (D n : ℝ) =
          r * L n ^ 3 := by
        dsimp [r]
        field_simp [ne_of_gt hLn]
      calc
        (D n : ℝ) ^ q = (r * L n ^ 3) ^ q := by rw [hsplit]
        _ = r ^ q * (L n ^ 3) ^ q :=
          Real.mul_rpow (hratioNonneg.trans_eq hr) (by positivity)
        _ = r ^ q * L n ^ p := by
          rw [← Real.rpow_natCast (L n) 3, ← Real.rpow_mul hLn.le]
          have hexp : (↑(3 : ℕ) : ℝ) * q = p := by dsimp [q]; ring
          rw [hexp]
    calc
      (D n : ℝ) ^ q / L n =
          (r ^ q * L n ^ p) / L n := by rw [hfactor]
      _ = r ^ q * L n ^ (p - 1) := by
        calc
          (r ^ q * L n ^ p) / L n = r ^ q * (L n ^ p / L n) := by ring
          _ = r ^ q * L n ^ (p - 1) := by
            have hquot : L n ^ p / L n = L n ^ (p - 1) := by
              calc
                L n ^ p / L n = L n ^ p / L n ^ (1 : ℝ) :=
                  congrArg (fun x : ℝ => L n ^ p / x)
                    (Real.rpow_one (L n)).symm
                _ = L n ^ (p - 1) := (Real.rpow_sub hLn p 1).symm
            rw [hquot]
      _ = ((D n : ℝ) / L n ^ 3) ^ q * L n ^ (p - 1) := by rw [hr]
  simpa [q] using hprod.congr' heq.symm

end Asymptotics
