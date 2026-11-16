/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import Probability.Sequence.IID.GeometricReward.ExponentialTransform

/-!
# Exponential moment of the displacement before the first split

## Internal proof declarations

* `exists_firstSplit_failureDisplacement_exponentialMoment`: the exponential
  moment of the signed displacement before the first split is
  $p_0/(1-A_\lambda)<\infty$, where
  $A_\lambda=\mathbb E[e^{\lambda\Xi_1}\mathbf 1_{B^c}]<1$ for some $\lambda>0$.
  The corresponding first-cycle displacement tail is bounded by
  $e^{-\lambda x}p_0/(1-A_\lambda)$.

This is the single-cycle transform in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1 at $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching
open Combinatorics.Branching.Step.FiniteSelection

private lemma exists_failureWeight_lt_one
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (hp : 0 < μ B)
    (Y : X → ℝ) (hY : Measurable Y)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀) (hexp : Integrable (fun x => Real.exp (lam₀ * Y x)) μ) :
    ∃ lam > (0 : ℝ), (∫⁻ x, ENNReal.ofReal (Real.exp (lam * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) < 1 := by
  let lam (n : ℕ) := lam₀ * (1 / ((n : ℝ) + 1))
  have hLam (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hLamle (n : ℕ) : lam n ≤ lam₀ := by
    dsimp [lam]
    exact mul_le_of_le_one_right hlam₀.le
      (div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity))
  let f (n : ℕ) := Bᶜ.indicator (fun x => Real.exp (lam n * Y x))
  have hf (n : ℕ) : Measurable (f n) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hY)).indicator hB.compl
  have hn (n : ℕ) (x : X) : 0 ≤ f n x := by
    by_cases hx : x ∈ B <;> simp [f, hx, (Real.exp_pos _).le]
  have hbound (n : ℕ) (x : X) : ‖f n x‖ ≤ 1 + Real.exp (lam₀ * Y x) := by
    rw [Real.norm_of_nonneg (hn n x)]
    by_cases hx : x ∈ Bᶜ
    · rw [show f n x = Real.exp (lam n * Y x) from Set.indicator_of_mem hx _]
      by_cases hy : 0 ≤ Y x
      · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hLamle n) hy)
        linarith
      · have he : Real.exp (lam n * Y x) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (hLam n).le (le_of_not_ge hy))
        linarith [Real.exp_pos (lam₀ * Y x)]
    · rw [show f n x = 0 from Set.indicator_of_notMem hx _]
      positivity
  have hdom := (integrable_const (1 : ℝ)).add hexp
  have hfi (n : ℕ) : Integrable (f n) μ :=
    hdom.mono' (hf n).aestronglyMeasurable (ae_of_all _ (hbound n))
  have hlim : Tendsto lam atTop (𝓝 0) := by
    simpa [lam] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul lam₀)
  have hconv : Tendsto (fun n => ∫ x, f n x ∂μ) atTop
      (𝓝 (∫ x, Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence _ (fun n => (hf n).aestronglyMeasurable)
      hdom (fun n => ae_of_all _ (hbound n))
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Bᶜ
    · have he : Tendsto (fun n => Real.exp (lam n * Y x)) atTop (𝓝 (Real.exp (0 * Y x))) :=
        Real.continuous_exp.continuousAt.tendsto.comp (hlim.mul_const (Y x))
      simpa [f, hx] using he
    · simp [f, hx]
  have hsmall : (∫ x, Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂μ) < 1 := by
    rw [integral_indicator_const _ hB.compl, measureReal_compl hB]
    simpa [measureReal_def] using (sub_lt_self (1 : ℝ)
      (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)))
  obtain ⟨n, hn'⟩ := (hconv.eventually_lt_const hsmall).exists
  refine ⟨lam n, hLam n, ?_⟩
  have heq (x : X) : ENNReal.ofReal (f n x) =
      ENNReal.ofReal (Real.exp (lam n * Y x)) * Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ Bᶜ <;> simp [f, hx]
  simp_rw [← heq]
  rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hn n))]
  exact ENNReal.ofReal_lt_one.mpr hn'

private lemma measure_firstFailureDisplacement_ge_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (step : ℕ → Ω → X) (hstep : ∀ n, Measurable (step n))
    (B : Set X) (hB : MeasurableSet B) (Y : X → ℝ) (hY : Measurable Y)
    (lam x : ℝ) (hlam : 0 < lam) :
    ENNReal.ofReal (Real.exp (lam * x)) *
      P {ω | ∃ n, step n ω ∈ B ∧ (∀ j < n, step j ω ∉ B) ∧
        x ≤ ∑ j ∈ Finset.range n, Y (step j ω)} ≤
      ∫⁻ ω, ∑' n, geometricFailureExponentialTerm step B Y lam n ω ∂P := by
  let weight (n : ℕ) := geometricFailureExponentialTerm step B Y lam n
  have hweight (n : ℕ) : Measurable (weight n) := by
    unfold weight geometricFailureExponentialTerm
    apply Finset.measurable_prod
    intro j _
    split
    · exact ((Real.continuous_exp.measurable.comp
        (measurable_const.mul (hY.comp (hstep j)))).ennreal_ofReal).mul
          ((measurable_const.indicator hB.compl).comp (hstep j))
    · exact (measurable_const.indicator hB).comp (hstep j)
  refine (mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le).trans
    (mul_meas_ge_le_lintegral (Measurable.tsum hweight) _)
  intro ω hω
  obtain ⟨n, hsuccess, hfail, hsum⟩ := hω
  have heq : weight n ω =
      ENNReal.ofReal (Real.exp (lam * ∑ j ∈ Finset.range n, Y (step j ω))) := by
    unfold weight geometricFailureExponentialTerm
    rw [Finset.prod_range_succ, ite_eq_right (Nat.lt_irrefl _),
      Set.indicator_of_mem hsuccess, mul_one, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro j hj
      rw [ite_eq_left (Finset.mem_range.mp hj), Set.indicator_of_mem (hfail j
        (Finset.mem_range.mp hj)), mul_one]
    · intro j _
      exact (Real.exp_pos _).le
  change ENNReal.ofReal (Real.exp (lam * x)) ≤ ∑' n, weight n ω
  calc
    _ ≤ weight n ω := by
      rw [heq]
      exact ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hlam.le))
    _ ≤ _ := le_tsum (f := fun j => weight j ω) n

lemma exists_firstSplit_failureDisplacement_exponentialMoment
    {Root ι X : Type*} [MeasurableSpace X]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hexp : HasLeftmostPositiveExponentialMoment L)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hp : 0 < L.sortedPotentialImage (splitBy R)) (r : Root) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    let Y := fun ξ : Step ℕ ℝ => value' ξ 0
    let B := splitBy R
    ∃ lam > (0 : ℝ), let A := ∫⁻ x, ENNReal.ofReal (Real.exp (lam * Y x)) *
          Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
      A < 1 ∧
        (∫⁻ ω, ∑' n, geometricFailureExponentialTerm (Coupling.step R r) B Y lam n ω ∂P) =
          μ B / (1 - A) ∧ μ B / (1 - A) < ∞ ∧
        ∀ x : ℝ, ENNReal.ofReal (Real.exp (lam * x)) *
          P {ω | ∃ n, Coupling.step R r n ω ∈ B ∧
            (∀ j < n, Coupling.step R r j ω ∉ B) ∧
            x ≤ ∑ j ∈ Finset.range n, Y (Coupling.step R r j ω)} ≤ μ B / (1 - A) := by
  let μ := L.sortedPotentialImage
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Y := fun ξ : Step ℕ ℝ => value' ξ 0
  let B := splitBy R
  have hB := splitBy_measurable R hR
  have hY : Measurable Y := value'_measurable 0
  obtain ⟨lam₀, hlam₀, hraw⟩ := hexp
  have hs : Integrable (fun ξ : Step ℕ X => Real.exp (lam₀ * ξ.potentialValue' L.potential 0))
      L.sorted := by
    rw [StepLaw.sorted]
    have hm : Measurable (fun ξ : Step ℕ X =>
        Real.exp (lam₀ * ξ.potentialValue' L.potential 0)) :=
      Real.continuous_exp.measurable.comp
        (measurable_const.mul (Step.potentialValue'_measurable L.potential 0))
    apply (integrable_map_measure hm.aestronglyMeasurable
      L.ordering.measurable_ordered.aemeasurable).2
    exact hraw
  have hμ : Integrable (fun ξ => Real.exp (lam₀ * Y ξ)) μ := by
    change Integrable _ (L.sorted.map (fun ξ => ξ.map L.potential))
    apply (integrable_map_measure ((Real.continuous_exp.measurable.comp
      (measurable_const.mul hY)).aestronglyMeasurable)
      (Step.map_measurable L.potential.measurable_toFun).aemeasurable).2
    exact hs
  obtain ⟨lam, hLam, hA⟩ := exists_failureWeight_lt_one μ B hB hp Y hY lam₀ hlam₀ hμ
  have htransform := iidGeometricFailureExponentialTransform P μ (Coupling.step R r)
    (Coupling.step_measurable R hR r) (Coupling.step_iIndepFun μ R hR r)
    (Coupling.step_law μ R hR r) B hB Y hY lam _ rfl _ rfl
  refine ⟨lam, hLam, hA, htransform, ?_, ?_⟩
  · exact ENNReal.div_lt_top (measure_ne_top _ _) (ne_of_gt (tsub_pos_of_lt hA))
  · intro x
    rw [← htransform]
    exact measure_firstFailureDisplacement_ge_le P (Coupling.step R r)
      (Coupling.step_measurable R hR r) B hB Y hY lam x hLam

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
