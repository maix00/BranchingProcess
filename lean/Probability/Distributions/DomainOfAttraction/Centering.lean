/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Sequence.IID
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Centering under uncentered attraction

An integrable increment law whose uncentered normalized i.i.d. sums converge
to a probability law must have zero mean whenever the normalization is
sublinear. The proof compares the strong law with scalar weak convergence
using a bounded continuous test function that vanishes at both infinities.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- Uncentered scalar attraction with sublinear normalization forces the
increment mean to vanish, provided that the first moment exists. The
sublinearity hypothesis is stated explicitly so this adapter does not assume
any regular-variation facts about the normalization. -/
theorem integral_eq_zero_of_uncenteredAttraction_of_sublinearNormalization
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hint : Integrable (fun x : ℝ => x) ν)
    (hsublinear : Tendsto (fun n : ℕ => normalization n / (n : ℝ))
      atTop (nhds 0)) :
    (∫ x : ℝ, x ∂ν) = 0 := by
  let sequenceLaw : Measure (ℕ → ℝ) := iidSequenceLaw ν
  let X : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i
  let S : ℕ → (ℕ → ℝ) → ℝ := fun n ω =>
    normalizedIidSum normalization (fun _ => 0) n ω
  let phi : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (-|x|), by fun_prop⟩ 1 (by
      intro x y
      have hx0 : 0 ≤ Real.exp (-|x|) := (Real.exp_pos _).le
      have hx1 : Real.exp (-|x|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
      have hy0 : 0 ≤ Real.exp (-|y|) := (Real.exp_pos _).le
      have hy1 : Real.exp (-|y|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg y))
      change |Real.exp (-|x|) - Real.exp (-|y|)| ≤ 1
      rw [abs_le]
      constructor <;> linarith)
  have hXmeas (i : ℕ) : Measurable (X i) := by
    exact measurable_pi_apply i
  have hident : ∀ i : ℕ,
      IdentDistrib (X i) (X 0) sequenceLaw sequenceLaw := by
    intro i
    refine ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, ?_⟩
    rw [iidSequenceLaw_map_apply ν i, iidSequenceLaw_map_apply ν 0]
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g sequenceLaw) X) := by
    intro i j hij
    exact (iidSequenceLaw_independent ν).indepFun hij
  have hXintegrable : Integrable (X 0) sequenceLaw := by
    have hid : IdentDistrib (X 0) (fun x : ℝ => x) sequenceLaw ν := by
      refine ⟨(hXmeas 0).aemeasurable, aemeasurable_id, ?_⟩
      rw [iidSequenceLaw_map_apply]
      simp
    exact hid.integrable_iff.mpr hint
  have hmeanEq : (∫ ω, X 0 ω ∂sequenceLaw) = ∫ x : ℝ, x ∂ν := by
    have hid : IdentDistrib (X 0) (fun x : ℝ => x) sequenceLaw ν := by
      refine ⟨(hXmeas 0).aemeasurable, aemeasurable_id, ?_⟩
      rw [iidSequenceLaw_map_apply]
      simp
    exact hid.integral_eq
  have hSLLN := strong_law_ae_real X hXintegrable hindep hident
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < normalization n := hDOA.1
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    exact (eventually_gt_atTop (0 : ℕ)).mono fun n hn => by exact_mod_cast hn
  have hdenPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization n / (n : ℝ) := by
    filter_upwards [hscalePos, hnatPos] with n hb hn
    exact div_pos hb hn
  have hdenWithin : Tendsto (fun n : ℕ => normalization n / (n : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsublinear, hdenPos⟩
  have hinvDen : Tendsto (fun n : ℕ => (normalization n / (n : ℝ))⁻¹)
      atTop atTop := tendsto_inv_nhdsGT_zero.comp hdenWithin
  have hphiNonneg (x : ℝ) : 0 ≤ phi x := (Real.exp_pos _).le
  have hphiLeOne (x : ℝ) : phi x ≤ 1 := by
    change Real.exp (-|x|) ≤ 1
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  have hphiIntegrable : Integrable (fun x : ℝ => phi x) μ := by
    refine Integrable.of_bound phi.continuous.aestronglyMeasurable 1
      (ae_of_all μ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hphiNonneg x)]
    exact hphiLeOne x
  have hphiLimitPos : 0 < ∫ x : ℝ, phi x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => hphiNonneg x)
      hphiIntegrable).2
    rw [show Function.support (fun x : ℝ => phi x) = Set.univ by
      ext x
      simp only [Function.support, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ne_of_gt (Real.exp_pos _)]
    rw [measure_univ]
    norm_num
  have hXevalMeas (n : ℕ) : Measurable (S n) := by
    dsimp [S]
    exact normalizedIidSum_measurable normalization (fun _ => 0) n
  have hphiMeas (n : ℕ) : AEStronglyMeasurable (fun ω => phi (S n ω)) sequenceLaw :=
    (phi.continuous.aemeasurable.comp_aemeasurable
      (hXevalMeas n).aemeasurable).aestronglyMeasurable
  have hphiBound (n : ℕ) : ∀ᵐ ω ∂sequenceLaw,
      ‖phi (S n ω)‖ ≤ 1 := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hphiNonneg _)]
    exact hphiLeOne _
  by_contra hmeanZero
  have hmeanNe : (∫ x : ℝ, x ∂ν) ≠ 0 := hmeanZero
  have hphiAEZero : ∀ᵐ ω ∂sequenceLaw,
      Tendsto (fun n : ℕ => phi (S n ω)) atTop (nhds 0) := by
    rcases lt_or_gt_of_ne hmeanNe with hmeanNeg | hmeanPos
    · filter_upwards [hSLLN] with ω hω
      have hnum : Tendsto
          (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
          atTop (nhds (∫ x : ℝ, x ∂ν)) := by
        simpa [hmeanEq] using hω
      have hnumNeg : Tendsto
          (fun n : ℕ => -((∑ i ∈ Finset.range n, X i ω) / (n : ℝ)))
          atTop (nhds (-(∫ x : ℝ, x ∂ν))) := hnum.neg
      have haux := hinvDen.atTop_mul_pos (neg_pos.mpr hmeanNeg) hnumNeg
      have hratioNeg : Tendsto (fun n : ℕ => -(S n ω)) atTop atTop := by
        have heqEventually : ((fun n : ℕ =>
            (normalization n / (n : ℝ))⁻¹ *
              (-((∑ i ∈ Finset.range n, X i ω) / (n : ℝ)))) =ᶠ[atTop]
            (fun n => -(S n ω))) := by
          filter_upwards [hscalePos, hnatPos] with n hb hn
          dsimp [S, normalizedIidSum, X]
          field_simp [ne_of_gt hb, ne_of_gt hn]
          ring
        exact haux.congr' heqEventually
      have habs := tendsto_abs_atTop_atTop.comp hratioNeg
      have hexp := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp habs)
      simpa [phi, Function.comp_def, abs_neg] using hexp
    · filter_upwards [hSLLN] with ω hω
      have hnum : Tendsto
          (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
          atTop (nhds (∫ x : ℝ, x ∂ν)) := by
        simpa [hmeanEq] using hω
      have haux := hinvDen.atTop_mul_pos hmeanPos hnum
      have heqEventually : ((fun n : ℕ =>
          (normalization n / (n : ℝ))⁻¹ *
            ((∑ i ∈ Finset.range n, X i ω) / (n : ℝ))) =ᶠ[atTop]
          (fun n => S n ω)) := by
        filter_upwards [hscalePos, hnatPos] with n hb hn
        dsimp [S, normalizedIidSum, X]
        field_simp [ne_of_gt hb, ne_of_gt hn]
        ring
      have hratio : Tendsto (fun n : ℕ => S n ω) atTop atTop :=
        haux.congr' heqEventually
      have habs := tendsto_abs_atTop_atTop.comp hratio
      have hexp := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp habs)
      simpa [phi, Function.comp_def] using hexp
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := sequenceLaw) (F := fun n ω => phi (S n ω)) (f := fun _ : ℕ → ℝ => (0 : ℝ))
    (bound := fun _ => 1) (Filter.Eventually.of_forall hphiMeas)
    (Filter.Eventually.of_forall hphiBound) (integrable_const (1 : ℝ)) hphiAEZero
  have hDOA_test := (tendstoInDistribution_iff_forall_integral_rclike_tendsto
    ℝ (fun n => (normalizedIidSum_measurable normalization (fun _ => 0) n).aemeasurable)
    aemeasurable_id).mp hDOA.2 phi
  have htestLimit : Tendsto (fun n : ℕ => ∫ ω, phi (S n ω) ∂sequenceLaw)
      atTop (nhds (∫ x : ℝ, phi x ∂μ)) := by
    simpa [S, sequenceLaw, Function.comp_def] using hDOA_test
  have hzeroLimit : Tendsto (fun n : ℕ => ∫ ω, phi (S n ω) ∂sequenceLaw)
      atTop (nhds 0) := by
    simpa using hDCT
  have hlimitEq := tendsto_nhds_unique htestLimit hzeroLimit
  linarith

end ProbabilityTheory

end
