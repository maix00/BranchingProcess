/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.MeasureTheory.Convergence.L2Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Second-moment convergence from polynomial tails

Polynomial tail bounds and logarithmic fourth-moment growth imply the tail
uniform-integrability estimate used to prove convergence in `L²`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

private lemma tendsto_one_add_log_eighth_div_rpow
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log (n : ℝ) ^ 8) / (n : ℝ) ^ p) atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ p) atTop atTop :=
    tendsto_rpow_atTop hp
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (hpow.comp tendsto_natCast_atTop_atTop)
  have hlogLittleReal : (fun x : ℝ => Real.log x ^ (8 : ℝ)) =o[atTop]
      fun x => x ^ p :=
    isLittleO_log_rpow_rpow_atTop 8 hp
  have hlogPowEq : (fun x : ℝ => Real.log x ^ (8 : ℝ)) =
      fun x => Real.log x ^ (8 : ℕ) := by
    funext x
    exact Real.rpow_natCast _ _
  have hlogLittle : (fun x : ℝ => Real.log x ^ (8 : ℕ)) =o[atTop]
      fun x => x ^ p :=
    hlogLittleReal.congr_left (fun x => by exact Real.rpow_natCast _ _)
  have hlog : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) ^ 8 / (n : ℝ) ^ p) atTop (nhds 0) :=
    hlogLittle.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsum := hinv.add hlog
  have heq : (fun n : ℕ =>
      (1 + Real.log (n : ℝ) ^ 8) / (n : ℝ) ^ p) =ᶠ[atTop]
      fun n => ((n : ℝ) ^ p)⁻¹ +
        Real.log (n : ℝ) ^ 8 / (n : ℝ) ^ p := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hsum' : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ p)⁻¹ +
        Real.log (n : ℝ) ^ 8 / (n : ℝ) ^ p)
      atTop (nhds 0) := by simpa using hsum
  exact hsum'.congr' heq.symm

/-- Polynomial decay of both tails, together with logarithmic fourth-moment
growth, makes the fourth-moment Hölder contribution vanish at every fixed
central threshold. -/
theorem tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ 8))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
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
      μ.real (bad n) ≤ Ctail / (n : ℝ) ^ p := by
    filter_upwards [htail] with n hn
    exact (measureReal_mono (hsubset n)).trans hn
  let fourth : ℕ → ℝ := fun n => ∫ ω, (X n ω) ^ 4 ∂μ
  let tail : ℕ → ℝ := fun n => μ.real (bad n)
  have hratio : Tendsto (fun n : ℕ =>
      (1 + Real.log (n : ℝ) ^ 8) / (n : ℝ) ^ p)
      atTop (nhds 0) := tendsto_one_add_log_eighth_div_rpow hp
  have hprodLimit : Tendsto (fun n : ℕ => fourth n * tail n)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ =>
        Cfourth * Ctail *
          ((1 + Real.log (n : ℝ) ^ 8) / (n : ℝ) ^ p))
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
        eventually_gt_atTop (0 : ℕ)] with n hM hT hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      have hfactorNonneg : 0 ≤ Cfourth * (1 + Real.log (n : ℝ) ^ 8) := by
        positivity
      have hmoment : fourth n ≤
          Cfourth * (1 + Real.log (n : ℝ) ^ 8) := by
        exact hM
      have htail' : tail n ≤ Ctail / (n : ℝ) ^ p := by
        exact hT
      have hTnonneg : 0 ≤ tail n := measureReal_nonneg
      have hprod := mul_le_mul hmoment htail' hTnonneg hfactorNonneg
      have hbound : fourth n * tail n ≤
          Cfourth * Ctail *
            ((1 + Real.log (n : ℝ) ^ 8) / (n : ℝ) ^ p) := by
        have hden : (n : ℝ) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn' p)
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

/-- Polynomial upper and lower tail estimates, together with logarithmic
fourth-moment growth, imply convergence to zero in `L²`. -/
theorem tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ 8))
    (htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p) :
    Tendsto (fun n => eLpNorm (X n) (2 : ℝ≥0∞) μ) atTop (nhds 0) :=
  tendsto_eLpNorm_two_zero_of_integral_sq μ X hX4
    (tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
      μ X hX hX4 hfourth htails)

/-- Centered polynomial tail bounds and logarithmic fourth-moment growth
imply `L²` convergence of a family to a fixed constant. -/
theorem tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (fun ω => X n ω - c) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ 8))
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
      (∫ ω, (Y n ω) ^ 4 ∂μ) ≤ C * (1 + Real.log (n : ℝ) ^ 8) := by
    simpa [Y] using hfourth
  have htailsY : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ Y n ω} ∪ {ω | Y n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p := by
    simpa [Y] using htails
  simpa [Y] using
    tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment
      μ Y hY hY4 hfourthY htailsY

/-- Centered polynomial tail bounds and logarithmic fourth-moment growth imply
convergence of the expectations to the center and of the variances to zero.
This is the moment form of the final `L²` convergence criterion. -/
theorem tendsto_integral_and_variance_of_polynomial_tails_log_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (fun ω => X n ω - c) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, (X n ω - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ 8))
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
      (∫ ω, (Y n ω) ^ 4 ∂μ) ≤ C * (1 + Real.log (n : ℝ) ^ 8) := by
    simpa [Y] using hfourth
  have htailsY : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({ω | ε ≤ Y n ω} ∪ {ω | Y n ω ≤ -ε}) ≤
          C / (n : ℝ) ^ p := by
    simpa [Y] using htails
  have hsecond : Tendsto (fun n => ∫ ω, (Y n ω) ^ 2 ∂μ)
      atTop (nhds 0) :=
    tendsto_integral_sq_of_polynomial_tails_log_fourth_moment
      μ Y hY hY4 hfourthY htailsY
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
