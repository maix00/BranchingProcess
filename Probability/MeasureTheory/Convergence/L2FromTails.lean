/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Basic
public import Mathlib.Tactic

/-!
# Second-moment convergence from tail control

These lemmas isolate the last measure-theoretic step in the trajectory
argument: control the squared variable on a small central interval directly,
and control its complement by Hölder's inequality and a fourth moment.

The public theorems in this file are:

- `ProbabilityTheory.integral_sq_le_threshold_add_fourthTail`: for
  $X\in L^4$ and $\varepsilon>0$,
  $\int X^2\,d\mu\le\varepsilon^2+
  (\int X^4\,d\mu)^{1/2}\,\mathbb P(|X|\ge\varepsilon)^{1/2}$.
- `ProbabilityTheory.tendsto_integral_sq_of_tendsto_fourthTailControl`:
  if for each fixed $\varepsilon>0$ the fourth-moment/tail contribution tends
  to zero, then $\int X_n^2\,d\mu\to0$.
- `ProbabilityTheory.tendsto_integral_sq_zero_of_uniform_fourthMoment_and_tails`:
  a uniform fourth-moment bound and vanishing two-sided fixed-threshold tails
  imply $\int X_n^2\,d\mu\to0$.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory

/-- Split a second moment at a symmetric interval. The complement contribution
is bounded by Hölder's inequality using the fourth moment. -/
theorem integral_sq_le_threshold_add_fourthTail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (hX4 : MemLp X (4 : ℝ≥0∞) μ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, (X ω) ^ 2 ∂μ) ≤ ε ^ 2 +
      Real.sqrt (∫ ω, (X ω) ^ 4 ∂μ) *
        Real.sqrt (μ.real {ω | ε ≤ |X ω|}) := by
  let F : Ω → ℝ := fun ω => (X ω) ^ 2
  let A : Set Ω := {ω | ε ≤ |X ω|}
  let μA : Measure Ω := μ.restrict A
  have h44 : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    rw [ENNReal.holderTriple_iff]
    rw [show (4 : ENNReal) = (↑(4 : NNReal) : ENNReal) by norm_num,
      show (2 : ENNReal) = (↑(2 : NNReal) : ENNReal) by norm_num]
    rw [← ENNReal.coe_inv (r := (4 : NNReal)) (by norm_num),
      ← ENNReal.coe_inv (r := (2 : NNReal)) (by norm_num)]
    norm_cast
    norm_num
  have hF2 : MemLp F 2 μ := by
    have hprod : MemLp (X * X) 2 μ := hX4.mul hX4 (hpqr := h44)
    have hfun : X * X = F := by
      funext ω
      simp [F, pow_two, Pi.mul_apply]
    have hnorm : ∀ᵐ ω ∂μ, ‖(X * X) ω‖ = ‖F ω‖ := by
      filter_upwards with ω
      rw [hfun]
    exact hprod.congr_norm (by fun_prop) hnorm
  have hF : Integrable F μ := hF2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF2Int : Integrable (fun ω => F ω ^ 2) μ := hF2.integrable_sq
  have hF_nonneg : 0 ≤ᵐ[μ] F := by
    exact ae_of_all μ (fun ω => sq_nonneg (X ω))
  have hF2_nonneg : 0 ≤ᵐ[μ] fun ω => F ω ^ 2 := by
    exact ae_of_all μ (fun ω => sq_nonneg (F ω))
  have hA : MeasurableSet A := by
    exact (measurableSet_Ici).preimage (by fun_prop : Measurable fun ω => |X ω|)
  have hF2A : MemLp F 2 μA := hF2.mono_measure Measure.restrict_le_self
  have hOneA : MemLp (fun _ : Ω => (1 : ℝ)) 2 μA := memLp_const _
  have hF_nonnegA : 0 ≤ᵐ[μA] F := ae_mono Measure.restrict_le_self hF_nonneg
  have hOne_nonnegA : 0 ≤ᵐ[μA] fun _ : Ω => (1 : ℝ) :=
    ae_of_all μA (fun _ => by norm_num)
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    exact Real.HolderConjugate.two_two
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μA) h22
    hF_nonnegA hOne_nonnegA (by simpa using hF2A) (by simpa using hOneA)
  have hF2Restrict :
      (∫ ω, F ω ^ 2 ∂μA) ≤ ∫ ω, F ω ^ 2 ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self hF2_nonneg hF2Int
  have hHolderSet :
      (∫ ω in A, F ω ∂μ) ≤
        Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    have hHolder' :
        (∫ ω in A, F ω ∂μ) ≤
          Real.sqrt (∫ ω, F ω ^ 2 ∂μA) *
          Real.sqrt ((μA).real Set.univ) := by
      simpa [μA, integral_const, smul_eq_mul, Real.sqrt_eq_rpow] using hHolder
    have hsqrt : Real.sqrt (∫ ω, F ω ^ 2 ∂μA) ≤
        Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := Real.sqrt_le_sqrt hF2Restrict
    have hmeasure : Real.sqrt ((μA).real Set.univ) = Real.sqrt (μ.real A) := by
      simp [μA]
    rw [hmeasure] at hHolder'
    exact hHolder'.trans
      (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))
  have hbad :
      (∫ ω in A, F ω ∂μ) ≤
        Real.sqrt (∫ ω, (X ω) ^ 4 ∂μ) * Real.sqrt (μ.real A) := by
    have hmoment : (∫ ω, F ω ^ 2 ∂μ) = ∫ ω, (X ω) ^ 4 ∂μ := by
      congr 1
      funext ω
      dsimp [F]
      ring
    rw [← hmoment]
    exact hHolderSet
  have hcomplMeasure : μ.real Aᶜ ≤ 1 := by
    calc
      μ.real Aᶜ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hgood : (∫ ω in Aᶜ, F ω ∂μ) ≤ ε ^ 2 := by
    calc
      (∫ ω in Aᶜ, F ω ∂μ) ≤
          ∫ ω in Aᶜ, (fun _ => ε ^ 2) ω ∂μ := by
        apply setIntegral_mono_on hF.integrableOn
          (integrable_const (ε ^ 2)).integrableOn hA.compl
        intro ω hω
        dsimp [A] at hω
        have habs : |X ω| < ε := lt_of_not_ge hω
        have habsle : |X ω| ≤ ε := habs.le
        change (X ω) ^ 2 ≤ ε ^ 2
        have hprod := mul_nonneg (sub_nonneg.mpr habsle)
          (show 0 ≤ ε + |X ω| by positivity)
        nlinarith [sq_abs (X ω), hprod]
      _ = μ.real Aᶜ * ε ^ 2 := by
        rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
      _ ≤ ε ^ 2 := by
        have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
        calc
          μ.real Aᶜ * ε ^ 2 ≤ 1 * ε ^ 2 :=
            mul_le_mul_of_nonneg_right hcomplMeasure hε2
          _ = ε ^ 2 := by ring
  have hsplit := integral_add_compl hA hF
  calc
    (∫ ω, (X ω) ^ 2 ∂μ) =
        (∫ ω in A, F ω ∂μ) + (∫ ω in Aᶜ, F ω ∂μ) := by
      simpa [F] using hsplit.symm
    _ ≤ Real.sqrt (∫ ω, (X ω) ^ 4 ∂μ) * Real.sqrt (μ.real A) + ε ^ 2 :=
      add_le_add hbad hgood
    _ = ε ^ 2 + Real.sqrt (∫ ω, (X ω) ^ 4 ∂μ) *
          Real.sqrt (μ.real A) := by ring
    _ = ε ^ 2 + Real.sqrt (∫ ω, (X ω) ^ 4 ∂μ) *
          Real.sqrt (μ.real {ω | ε ≤ |X ω|}) := by rfl

/-- If, for each fixed central interval, the Hölder bound on the tail tends to
zero, then the second moments tend to zero. Polynomial tail estimates combined
with a polylogarithmic fourth-moment bound supply this input in the trajectory
application. -/
theorem tendsto_integral_sq_of_tendsto_fourthTailControl
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hcontrol : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => Real.sqrt (∫ ω, (X n ω) ^ 4 ∂μ) *
        Real.sqrt (μ.real {ω | ε ≤ |X n ω|}))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂μ) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hnonneg (n : ℕ) : 0 ≤ ∫ ω, (X n ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (X n ω))
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hb (hnonneg n)
  · intro b hb
    let ε := min 1 (b / 4)
    have hε : 0 < ε := lt_min zero_lt_one (by linarith)
    have hεle1 : ε ≤ 1 := min_le_left _ _
    have hεle : ε ≤ b / 4 := min_le_right _ _
    have hεsq : ε ^ 2 < b / 2 := by
      have hεnonneg : 0 ≤ ε := hε.le
      have hsquare : ε ^ 2 ≤ ε := by nlinarith
      linarith
    have hcontrol' := hcontrol ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop,
        Real.sqrt (∫ ω, (X n ω) ^ 4 ∂μ) *
          Real.sqrt (μ.real {ω | ε ≤ |X n ω|}) < b / 2 :=
      hcontrol'.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hsmall] with n hn
    have hbound := integral_sq_le_threshold_add_fourthTail μ (X n)
      (hX n) (hX4 n) hε
    have hsum : ε ^ 2 +
        Real.sqrt (∫ ω, (X n ω) ^ 4 ∂μ) *
          Real.sqrt (μ.real {ω | ε ≤ |X n ω|}) < b := by
      linarith
    have hbound' : (∫ ω, (X n ω) ^ 2 ∂μ) < b :=
      lt_of_le_of_lt hbound hsum
    exact hbound'

/-- Two one-sided tail bounds and a uniform fourth-moment bound imply
convergence of the second moments to zero. This is the final measure-theoretic
step used to turn the two endpoint estimates for a normalized trajectory into
an `L²` limit. -/
theorem tendsto_integral_sq_zero_of_uniform_fourthMoment_and_tails
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hfourth : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, (∫ ω, (X n ω) ^ 4 ∂μ) ≤ C)
    (hupper : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ.real {ω | ε ≤ X n ω}) atTop (nhds 0))
    (hlower : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ.real {ω | X n ω ≤ -ε}) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂μ) atTop (nhds 0) := by
  rcases hfourth with ⟨C, hC, hfourth⟩
  have hcontrol' : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => Real.sqrt (∫ ω, (X n ω) ^ 4 ∂μ) *
        Real.sqrt (μ.real {ω | ε ≤ |X n ω|})) atTop (nhds 0) := by
    intro ε hε
    have htail : Tendsto
        (fun n => μ.real {ω | ε ≤ |X n ω|}) atTop (nhds 0) := by
      have hup := hupper ε hε
      have hlow := hlower ε hε
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun n => measureReal_nonneg
      · exact Filter.Eventually.of_forall fun n => by
          have hsubset : {ω | ε ≤ |X n ω|} ⊆
              {ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε} := by
            intro ω hω
            by_cases hnonneg : 0 ≤ X n ω
            · left
              simpa [abs_of_nonneg hnonneg] using hω
            · right
              have hneg : X n ω < 0 := lt_of_not_ge hnonneg
              have habs : |X n ω| = -X n ω := abs_of_neg hneg
              change ε ≤ |X n ω| at hω
              rw [habs] at hω
              change X n ω ≤ -ε
              linarith
          calc
            μ.real {ω | ε ≤ |X n ω|} ≤
                μ.real ({ω | ε ≤ X n ω} ∪ {ω | X n ω ≤ -ε}) :=
              measureReal_mono hsubset
            _ ≤ μ.real {ω | ε ≤ X n ω} + μ.real {ω | X n ω ≤ -ε} :=
              measureReal_union_le _ _
      · simpa using hup.add hlow
    have htailSqrt : Tendsto
        (fun n => Real.sqrt (μ.real {ω | ε ≤ |X n ω|})) atTop (nhds 0) := by
      simpa using htail.sqrt
    let fourth : ℕ → ℝ := fun n => ∫ ω, (X n ω) ^ 4 ∂μ
    let tail : ℕ → ℝ := fun n => μ.real {ω | ε ≤ |X n ω|}
    have hcontrol : Tendsto
        (fun n => Real.sqrt (fourth n) * Real.sqrt (tail n)) atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun n =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · exact Filter.Eventually.of_forall fun n => by
          have hsqrt : Real.sqrt (fourth n) ≤ Real.sqrt C :=
            Real.sqrt_le_sqrt (hfourth n)
          exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      · simpa [tail] using (tendsto_const_nhds.mul htailSqrt)
    simpa [fourth, tail] using hcontrol
  exact tendsto_integral_sq_of_tendsto_fourthTailControl μ X hX hX4 hcontrol'

end ProbabilityTheory

end
