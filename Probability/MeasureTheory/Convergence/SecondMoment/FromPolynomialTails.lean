/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.MeasureTheory.Convergence.SecondMoment.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Second-moment convergence from polynomial tails

Polynomial tail bounds and logarithmic fourth-moment growth imply the tail
uniform-integrability estimate used to prove convergence in `L²`.

## Public declarations

- `ProbabilityTheory.tendsto_integral_sq_of_polynomial_tails_log_fourth_moment`:
  for each $q\in\mathbb R$, if eventually
  $\int X_n^4\,d\mu\le C(1+(\log n)^q)$ and, for every $\varepsilon>0$,
  $\mu(\{\varepsilon\le X_n\}\cup\{X_n\le-\varepsilon\})
  \le C_\varepsilon n^{-p_\varepsilon}$ for some $C_\varepsilon,p_\varepsilon>0$,
  then $\int X_n^2\,d\mu\to0$.
- `ProbabilityTheory.tendsto_integral_sq_of_polynomial_tails_log_fourth_moment_of_scale`:
  the same conclusion holds along any scale $r_n\to\infty$ when the fourth
  moments grow as $1+(\log r_n)^q$ and both tails decay as $r_n^{-p}$.
- `ProbabilityTheory.tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment_of_scale`:
  under the corresponding centered hypotheses, the $L^2$ distance satisfies
  $\|X_n-c\|_{L^2(\mu)}\to0$ along the same arbitrary scale.
- `ProbabilityTheory.tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment`:
  the same assumptions imply $\|X_n\|_{L^2}\to0$.
- `ProbabilityTheory.tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment`:
  the centered versions of those assumptions imply
  $\|X_n-c\|_{L^2}\to0$.
- `ProbabilityTheory.tendsto_integral_and_variance_of_polynomial_tails_log_fourth_moment`:
  the centered assumptions imply $\mathbb E[X_n]\to c$ and
  $\operatorname{Var}(X_n)\to0$.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

private lemma tendsto_one_add_log_rpow_div_rpow_of_scale (q : ℝ)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (scale n) ^ q) / (scale n) ^ p) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (scale n) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp hscale
  have hinv : Tendsto (fun n : ℕ => ((scale n) ^ p)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hlogLittle : (fun x : ℝ => Real.log x ^ q) =o[atTop]
      fun x => x ^ p :=
    isLittleO_log_rpow_rpow_atTop q hp
  have hlog : Tendsto (fun n : ℕ =>
      Real.log (scale n) ^ q / (scale n) ^ p) atTop (nhds 0) :=
    hlogLittle.tendsto_div_nhds_zero.comp hscale
  have hsum := hinv.add hlog
  have heq : (fun n : ℕ =>
      (1 + Real.log (scale n) ^ q) / (scale n) ^ p) =ᶠ[atTop]
      fun n => ((scale n) ^ p)⁻¹ +
        Real.log (scale n) ^ q / (scale n) ^ p := by
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    have hn' : 0 < scale n := hn
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hsum' : Tendsto
      (fun n : ℕ => ((scale n) ^ p)⁻¹ +
        Real.log (scale n) ^ q / (scale n) ^ p)
      atTop (nhds 0) := by simpa using hsum
  exact hsum'.congr' heq.symm

/-- Polynomial decay of both tails, together with logarithmic fourth-moment
growth, makes the fourth-moment Hölder contribution vanish at every fixed
central threshold. -/
theorem tendsto_integral_sq_of_polynomial_tails_log_fourth_moment_of_scale
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤
        C * (1 + Real.log (scale n) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (scale n) ^ p) :
    Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂μ) atTop (nhds 0) := by
  apply tendsto_integral_sq_of_tendsto_fourthTailControl μ X hX hX4
  intro ε hε
  obtain ⟨Ctail, p, hCtail, hp, htail⟩ := htails ε hε
  obtain ⟨Cfourth, hCfourth, hfourthEventually⟩ := hfourth
  let bad : ℕ → Set Ω := fun n => {ω | ε ≤ |X n ω|}
  let unionBad : ℕ → Set Ω := fun n =>
    {ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}
  have hsubset (n : ℕ) : bad n ⊆ unionBad n := by
    intro ω hω
    change ε ≤ |X n ω| at hω
    by_cases hnonneg : 0 ≤ X n ω
    · left
      simpa [unionBad, abs_of_nonneg hnonneg] using hω
    · right
      have hneg : X n ω < 0 := lt_of_not_ge hnonneg
      have habs : |X n ω| = -X n ω := abs_of_neg hneg
      have hω' : ε ≤ -X n ω := by simpa [habs] using hω
      change X n ω ≤ -ε
      linarith
  have hbadBound : ∀ᶠ n : ℕ in atTop,
      μ.real (bad n) ≤ Ctail / (scale n) ^ p := by
    filter_upwards [htail] with n hn
    exact (measureReal_mono (hsubset n)).trans hn
  let fourth : ℕ → ℝ := fun n => ∫ ω, (X n ω) ^ 4 ∂μ
  let tail : ℕ → ℝ := fun n => μ.real (bad n)
  have hratio : Tendsto (fun n : ℕ =>
      (1 + Real.log (scale n) ^ q) / (scale n) ^ p)
      atTop (nhds 0) :=
    tendsto_one_add_log_rpow_div_rpow_of_scale q hscale hp
  have hprodLimit : Tendsto (fun n : ℕ => fourth n * tail n)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ =>
        Cfourth * Ctail *
          ((1 + Real.log (scale n) ^ q) / (scale n) ^ p))
        atTop (nhds 0) := by
      have h := hratio.const_mul (Cfourth * Ctail)
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hfourthNonneg (n : ℕ) : 0 ≤ fourth n := by
      exact integral_nonneg (fun ω => by positivity)
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        mul_nonneg (hfourthNonneg n)
          (measureReal_nonneg)
    · filter_upwards [hfourthEventually, hbadBound,
        hscale.eventually_gt_atTop 1] with n hM hT hn
      have hn' : 0 < scale n := lt_trans (by norm_num) hn
      have hlog : 0 ≤ Real.log (scale n) := Real.log_nonneg (le_of_lt hn)
      have hfactorNonneg : 0 ≤ Cfourth * (1 + Real.log (scale n) ^ q) := by
        positivity
      have hmoment : fourth n ≤
          Cfourth * (1 + Real.log (scale n) ^ q) := by
        exact hM
      have htail' : tail n ≤ Ctail / (scale n) ^ p := by
        exact hT
      have hTnonneg : 0 ≤ tail n := measureReal_nonneg
      have hprod := mul_le_mul hmoment htail' hTnonneg hfactorNonneg
      have hbound : fourth n * tail n ≤
          Cfourth * Ctail *
            ((1 + Real.log (scale n) ^ q) / (scale n) ^ p) := by
        have hden : (scale n) ^ p ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos hn' p)
        simpa [fourth, tail, div_eq_mul_inv, mul_assoc, mul_left_comm,
          mul_comm] using hprod
      exact hbound
    · exact hupper
  let control : ℕ → ℝ := fun n =>
    Real.sqrt (fourth n) * Real.sqrt (tail n)
  have hcontrol : Tendsto control atTop (nhds 0) := by
    have hfourthNonneg (n : ℕ) : 0 ≤ fourth n := by
      exact integral_nonneg (fun ω => by positivity)
    have hcontrolSq : ∀ n, control n = Real.sqrt (fourth n * tail n) := by
      intro n
      simp [control, Real.sqrt_mul (hfourthNonneg n)]
    have h := hprodLimit.sqrt
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (fourth n * tail n))
        atTop (nhds 0) := by simpa using h
    apply hsqrt.congr'
    filter_upwards with n
    exact (hcontrolSq n).symm
  simpa [control, fourth, tail, bad] using hcontrol

/-- Polynomial tails and logarithmic fourth-moment growth at the natural
index are the specialization of
`tendsto_integral_sq_of_polynomial_tails_log_fourth_moment_of_scale` to
`rₙ=n`. -/
theorem tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
    Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂μ) atTop (nhds 0) := by
  let scale : ℕ → ℝ := fun n => n
  have hscale : Tendsto scale atTop atTop := by
    simpa [scale] using tendsto_natCast_atTop_atTop
  have hfourth' : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤ C * (1 + Real.log (scale n) ^ q) := by
    simpa [scale] using hfourth
  have htails' : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (scale n) ^ p := by
    simpa [scale] using htails
  simpa using
    tendsto_integral_sq_of_polynomial_tails_log_fourth_moment_of_scale
      q μ X scale hscale hX hX4 hfourth' htails'

/-- Centered polynomial tails and logarithmic fourth-moment growth at any
diverging real scale imply convergence to the center in `L²`. -/
theorem tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment_of_scale
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (fun ω => X n ω - c) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (scale n) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω - c} ∪ {ω | X n ω - c ≤ -ε}) ≤
          C / (scale n) ^ p) :
    Tendsto (fun n => eLpNorm (fun ω => X n ω - c)
      (2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  let Y : ℕ → Ω → ℝ := fun n ω => X n ω - c
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    exact (hX n).sub measurable_const
  have hY2 : ∀ n, MemLp (Y n) (2 : ℝ≥0∞) μ := by
    intro n
    exact (hX4 n).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hsecond : Tendsto (fun n => ∫ ω, (Y n ω) ^ 2 ∂μ)
      atTop (nhds 0) := by
    apply tendsto_integral_sq_of_polynomial_tails_log_fourth_moment_of_scale
      q μ Y scale hscale hY hX4
    · simpa [Y] using hfourth
    · simpa [Y] using htails
  simpa [Y] using tendsto_eLpNorm_two_zero_of_integral_sq μ Y hY2 hsecond

/-- Polynomial upper and lower tail estimates, together with logarithmic
fourth-moment growth, imply convergence to zero in `L²`. -/
theorem tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
    Tendsto (fun n => eLpNorm (X n) (2 : ℝ≥0∞) μ) atTop (nhds 0) :=
  by
    have hX2 : ∀ n, MemLp (X n) (2 : ℝ≥0∞) μ := fun n =>
      (hX4 n).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    exact tendsto_eLpNorm_two_zero_of_integral_sq μ X hX2
      (tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
        q μ X hX hX4 hfourth htails)

/-- Centered polynomial tail bounds and logarithmic fourth-moment growth
imply `L²` convergence of a family to a fixed constant. -/
theorem tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (fun ω => X n ω - c) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω - c} ∪ {ω | X n ω - c ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
    Tendsto (fun n => eLpNorm (fun ω => X n ω - c)
      (2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  let Y : ℕ → Ω → ℝ := fun n ω => X n ω - c
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    exact (hX n).sub measurable_const
  have hY4 : ∀ n, MemLp (Y n) (4 : ℝ≥0∞) μ := hX4
  have hfourthY : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (Y n ω) ^ 4 ∂μ) ≤ C * (1 + Real.log (n : ℝ) ^ q) := by
    simpa [Y] using hfourth
  have htailsY : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ Y n ω} ∪ {ω | Y n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p := by
    simpa [Y] using htails
  simpa [Y] using
    tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment
      q μ Y hY hY4 hfourthY htailsY

/-- Centered polynomial tail bounds and logarithmic fourth-moment growth imply
convergence of the expectations to the center and of the variances to zero.
This is the moment form of the final `L²` convergence criterion. -/
theorem tendsto_integral_and_variance_of_polynomial_tails_log_fourth_moment
    (q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (fun ω => X n ω - c) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ q))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω - c} ∪ {ω | X n ω - c ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (nhds c) ∧
      Tendsto (fun n => variance (X n) μ) atTop (nhds 0) := by
  let Y : ℕ → Ω → ℝ := fun n ω => X n ω - c
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    exact (hX n).sub measurable_const
  have hY4 : ∀ n, MemLp (Y n) (4 : ℝ≥0∞) μ := hX4
  have hfourthY : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (Y n ω) ^ 4 ∂μ) ≤ C * (1 + Real.log (n : ℝ) ^ q) := by
    simpa [Y] using hfourth
  have htailsY : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ Y n ω} ∪ {ω | Y n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p := by
    simpa [Y] using htails
  have hsecond : Tendsto (fun n => ∫ ω, (Y n ω) ^ 2 ∂μ)
      atTop (nhds 0) :=
    tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
      q μ Y hY hY4 hfourthY htailsY
  have hX2 : ∀ n, MemLp (X n) (2 : ℝ≥0∞) μ := by
    intro n
    have h := (hX4 n).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    have hshift : X n = (fun ω : Ω => X n ω - c) + (fun _ : Ω => c) := by
      funext ω
      exact (sub_add_cancel (X n ω) c).symm
    rw [hshift]
    exact h.add (memLp_const c)
  exact tendsto_integral_and_variance_of_tendsto_centered_integral_sq
    μ X c hX2 (by simpa [Y] using hsecond)

end ProbabilityTheory

end
