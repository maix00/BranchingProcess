/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Basic

public section

/-!
# Asymptotically equivalent random variables

Convergence in distribution is unchanged when two sequences, realized on the
same probability spaces, admit a measurable error bound tending to zero in
probability.  This formulation applies to nonlinear path spaces without
requiring measurability of their distance as an extra global assumption.

The public theorems are:

- `MeasureTheory.tendstoInDistribution_of_error_tendstoInMeasure`:
  transfer convergence along a vanishing metric error.
- `MeasureTheory.tendstoInDistribution_of_negligible_disagreement`:
  transfer convergence when the probability that two coupled random variables
  differ tends to zero.
- `MeasureTheory.abs_integral_sub_le_oscillation_mul_disagreement`:
  bound the difference of two expectations by the disagreement probability
  times an oscillation bound for the observable.
-/

open Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory

variable {I E Ω' Ω'' : Type*}
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} [MetricSpace E] [BorelSpace E]
  {l : Filter I} {X Y : I → Ω'' → E} {Z : Ω' → E}
  {error : I → Ω'' → ℝ}

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` converges in distribution to `Z` and a measurable nonnegative
upper bound for the distance from `Y` to `X` converges to zero in
probability, then `Y` converges in distribution to `Z`.
-/
theorem tendstoInDistribution_of_error_tendstoInMeasure
    [l.IsCountablyGenerated]
    (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ')
    (herror_meas : ∀ i, AEMeasurable (error i) μ'')
    (hdist : ∀ i ω, dist (Y i ω) (X i ω) ≤ error i ω)
    (herror : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i => μ''.real {ω | ε ≤ error i ω}) l (nhds 0))
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution Y l Z (fun _ => μ'') μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  suffices ∀ (F : E → ℝ)
      (_hF_bounded : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
      (_hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n => ∫ ω, F ω ∂(μ''.map (Y n))) l
        (nhds (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l,
      |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n :
      |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| ≤
        L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ error n ω} +
          |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n)))
      (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    have hF_Y : AEStronglyMeasurable (fun x => F (Y n x)) μ'' :=
      (hF_cont.aemeasurable.comp_aemeasurable (hY n)).aestronglyMeasurable
    have hF_X : AEStronglyMeasurable (fun x => F (X n x)) μ'' :=
      (hF_cont.aemeasurable.comp_aemeasurable (hX n)).aestronglyMeasurable
    have h_int_Y : Integrable (fun x => F (Y n x)) μ'' := by
      refine Integrable.of_bound hF_Y (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x => F (X n x)) μ'' := by
      refine Integrable.of_bound hF_X (‖F x₀‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a => ‖F (Y n a) - F (X n a)‖) μ'' := by
      exact (h_int_Y.sub h_int_X).norm
    rw [integral_map (hY n) hF_cont.aestronglyMeasurable,
      integral_map (hX n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc
      ‖∫ a, F (Y n a) - F (X n a) ∂μ''‖ ≤
          ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ'' :=
        norm_integral_le_integral_norm _
      _ = ∫ a in {x | error n x < ε / 2},
            ‖F (Y n a) - F (X n a)‖ ∂μ'' +
          ∫ a in {x | ε / 2 ≤ error n x},
            ‖F (Y n a) - F (X n a)‖ ∂μ'' := by
        symm
        simp_rw [← not_lt]
        refine integral_add_compl₀ ?_ h_int_sub
        exact nullMeasurableSet_lt (herror_meas n) (by fun_prop)
      _ ≤ ∫ _a in {x | error n x < ε / 2}, L * (ε / 2) ∂μ'' +
          ∫ _a in {x | ε / 2 ≤ error n x}, M ∂μ'' := by
        gcongr ?_ + ?_
        · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
          · exact nullMeasurableSet_lt (herror_meas n) (by fun_prop)
          · exact fun x hx => hF_lip.dist_le_mul_of_le ((hdist n x).trans hx.le)
        · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
          rw [← dist_eq_norm]
          exact hF_bounded _ _
      _ = L * (ε / 2) * μ''.real {x | error n x < ε / 2} +
          M * μ''.real {ω | ε / 2 ≤ error n ω} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
          Set.univ_inter, smul_eq_mul]
        ring
      _ ≤ L * (ε / 2) +
          M * μ''.real {ω | ε / 2 ≤ error n ω} := by
        rw [mul_assoc]
        gcongr
        grw [measureReal_le_one, mul_one]
  have h_tendsto : Tendsto
      (fun n => L * (ε / 2) +
        M * μ''.real {ω | ε / 2 ≤ error n ω} +
        |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|)
      l (nhds (L * ε / 2)) := by
    suffices Tendsto
        (fun n => L * (ε / 2) +
          M * μ''.real {ω | ε / 2 ≤ error n ω} +
          |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|)
        l (nhds (L * ε / 2 + M * 0 + 0)) by simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · exact herror (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using!
        hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn
  exact (h_le n).trans_lt hn

/-- A coupling may be changed on events whose probabilities tend to zero
without changing its limiting distribution. -/
theorem tendstoInDistribution_of_negligible_disagreement
    [l.IsCountablyGenerated] [SecondCountableTopology E]
    (hXZ : TendstoInDistribution X l Z (fun _ => μ'') μ')
    (hY : ∀ i, Measurable (Y i))
    (hbad : Tendsto (fun i => μ''.real {ω | Y i ω ≠ X i ω}) l (nhds 0)) :
    TendstoInDistribution Y l Z (fun _ => μ'') μ' := by
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  let error (i : I) (ω : Ω'') := dist (Y i ω) (X i ω)
  have herror_meas (i : I) : AEMeasurable (error i) μ'' :=
    (hY i).aemeasurable.dist (hX i)
  have herror (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun i => μ''.real {ω | ε ≤ error i ω}) l (nhds 0) := by
    have hbound (i : I) :
        μ''.real {ω | ε ≤ error i ω} ≤
          μ''.real {ω | Y i ω ≠ X i ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      exact fun heq => (not_le_of_gt hε) (by simpa [error, heq] using hω)
    have hnonneg (i : I) : 0 ≤ μ''.real {ω | ε ≤ error i ω} :=
      measureReal_nonneg
    exact squeeze_zero hnonneg hbound hbad
  exact tendstoInDistribution_of_error_tendstoInMeasure hXZ
    herror_meas (fun i ω => le_rfl) herror
    (fun i => (hY i).aemeasurable)

/-- The expectation of an observable changes by at most its oscillation
times the probability that two coupled variables disagree. -/
theorem abs_integral_sub_le_oscillation_mul_disagreement
    {E' : Type*} [MeasurableSpace E'] [MeasurableEq E'] [TopologicalSpace E']
    [OpensMeasurableSpace E']
    {μ : Measure Ω''} [IsProbabilityMeasure μ]
    {U V : Ω'' → E'} (hU : Measurable U) (hV : Measurable V)
    {F : E' → ℝ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ x y, dist (F x) (F y) ≤ M) :
    |∫ ω, F (U ω) ∂μ - ∫ ω, F (V ω) ∂μ| ≤
      M * μ.real {ω | U ω ≠ V ω} := by
  classical
  let bad : Set Ω'' := {ω | U ω ≠ V ω}
  have hbad : MeasurableSet bad :=
    (measurableSet_eq_fun hU hV).compl
  let x₀ : E' := U (nonempty_of_isProbabilityMeasure μ).some
  have hM_nonneg : 0 ≤ M :=
    (dist_nonneg : 0 ≤ dist (F x₀) (F x₀)).trans (hM x₀ x₀)
  have hFU : Integrable (fun ω => F (U ω)) μ := by
    apply Integrable.of_bound (hF.measurable.comp hU).aestronglyMeasurable
      (‖F x₀‖ + M)
    filter_upwards [] with ω
    have h := hM (U ω) x₀
    rw [Real.dist_eq] at h
    calc
      ‖F (U ω)‖ = ‖F x₀ + (F (U ω) - F x₀)‖ := by congr 1; ring
      _ ≤ ‖F x₀‖ + ‖F (U ω) - F x₀‖ := norm_add_le _ _
      _ ≤ ‖F x₀‖ + M := by
        simpa only [Real.norm_eq_abs] using add_le_add_right h ‖F x₀‖
  have hFV : Integrable (fun ω => F (V ω)) μ := by
    apply Integrable.of_bound (hF.measurable.comp hV).aestronglyMeasurable
      (‖F x₀‖ + M)
    filter_upwards [] with ω
    have h := hM (V ω) x₀
    rw [Real.dist_eq] at h
    calc
      ‖F (V ω)‖ = ‖F x₀ + (F (V ω) - F x₀)‖ := by congr 1; ring
      _ ≤ ‖F x₀‖ + ‖F (V ω) - F x₀‖ := norm_add_le _ _
      _ ≤ ‖F x₀‖ + M := by
        simpa only [Real.norm_eq_abs] using add_le_add_right h ‖F x₀‖
  have hnorm : Integrable (fun ω => ‖F (U ω) - F (V ω)‖) μ :=
    (hFU.sub hFV).norm
  rw [← integral_sub hFU hFV, ← Real.norm_eq_abs]
  calc
    ‖∫ ω, F (U ω) - F (V ω) ∂μ‖ ≤
        ∫ ω, ‖F (U ω) - F (V ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, bad.indicator (fun _ => M) ω ∂μ := by
      apply integral_mono hnorm
        ((integrable_const M (μ := μ)).integrableOn.integrable_indicator hbad)
      intro ω
      by_cases h : U ω = V ω
      · simp [bad, Set.indicator, h]
      · simpa [bad, Set.indicator, h, Real.dist_eq] using hM (U ω) (V ω)
    _ = M * μ.real bad := by
      rw [integral_indicator hbad, integral_const]
      simp [smul_eq_mul, mul_comm]

end MeasureTheory
