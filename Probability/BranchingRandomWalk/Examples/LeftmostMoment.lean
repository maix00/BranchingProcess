/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Replicated
public import Probability.Distributions.Moments.Real
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weak reproductive tails and an infinite leftmost first moment

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Examples.exists_boundaryLaw_spinalWeightTail_not_integrable_leftmost`:
  there exists a nonempty binary law with `∫W dμ=1`, centered spinal
  variance `σ²>0`, and `x² μ̂{log W+X>x}→0`, while
  `Y⁺∉L¹(μ)` for the leftmost displacement `Y`.

Both sibling displacements agree, so their relative spinal mark is `log 2`.
The positive displacement component is `8+2^G`, with `G` geometric of
parameter `1/2`. Atoms at `-1` and `0` normalize the boundary and spinal mean.

This separates the raw extreme-child moment from the reproductive condition
(1.9) of B. Mallein, *N-branching random walk with α-stable spine*,
Theorem 1.1, arXiv:1503.03762v2. The native geometric measure, measure sums,
exponential bias and replicated-offspring identities are used directly.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Examples
open MeasureTheory Combinatorics.Branching Spine Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

private noncomputable def halfParameter : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
private noncomputable def height (n : ℕ) : ℝ := 8 + (2 : ℝ) ^ n
private noncomputable def heavy : Measure ℝ :=
  (geometricMeasure halfParameter).map height
private instance heavy_probability : IsProbabilityMeasure heavy := by
  unfold heavy
  infer_instance

private lemma height_ge (n : ℕ) : 9 ≤ height n := by
  have := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 2)
  dsimp [height]
  linarith

private lemma heavy_weighted_moment (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x)) heavy := by
  have hheight : Tendsto height atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp [height]; linarith)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hheight
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  apply (integrable_map_measure (by fun_prop)
    (measurable_of_countable height).aemeasurable).mpr
  refine (integrable_const C).mono' (measurable_of_countable _).aestronglyMeasurable ?_
  exact ae_of_all _ (fun n => hC _ ⟨n, rfl⟩)

private lemma heavy_support : ∀ᵐ x ∂heavy, 9 ≤ x := by
  apply (ae_map_iff (measurable_of_countable height).aemeasurable measurableSet_Ici).mpr
  exact ae_of_all _ height_ge

private lemma heavy_not_integrable : ¬ Integrable (fun x : ℝ => max x 0) heavy := by
  intro h
  have hp : halfParameter ≠ 0 := ne_of_gt (show (0 : unitInterval) < halfParameter from by
    change (0 : ℝ) < 1 / 2
    norm_num)
  have hsum := (integrable_geometricMeasure_iff hp).mp
    (h.comp_measurable (measurable_of_countable height))
  have hc : Summable (fun _ : ℕ => (1 / 2 : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by norm_num) _ hsum
    intro n
    change (1 / 2 : ℝ) ≤ (1 - (halfParameter : ℝ)) ^ n *
      (halfParameter : ℝ) * ‖max (height n) 0‖
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _),
      max_eq_left ((by linarith [height_ge n]) : 0 ≤ height n)]
    norm_num only [halfParameter, Subtype.coe_mk]
    have he : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    dsimp [height]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hz := (summable_const_iff (1 / 2 : ℝ)).mp hc
  norm_num at hz

private noncomputable def a : ℝ := ∫ x, Real.exp (-x) ∂heavy
private noncomputable def b : ℝ := ∫ x, x * Real.exp (-x) ∂heavy

private lemma heavy_exp_integrable : Integrable (fun x : ℝ => Real.exp (-x)) heavy := by
  simpa using heavy_weighted_moment 0
private lemma heavy_mul_exp_integrable : Integrable (fun x : ℝ => x * Real.exp (-x)) heavy := by
  simpa using heavy_weighted_moment 1

private lemma coefficient_bounds : 0 ≤ a ∧ 0 < b ∧ a + b ≤ 1 / 4 := by
  have ha : 0 ≤ a := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hb : 0 < b := by
    apply (integral_pos_iff_support_of_nonneg_ae _ heavy_mul_exp_integrable).mpr
    · have he : Function.support (fun x : ℝ => x * Real.exp (-x)) =ᵐ[heavy] Set.univ := by
        filter_upwards [heavy_support] with x hx
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (mul_pos (by linarith) (Real.exp_pos _))
      rw [measure_congr he, measure_univ]
      norm_num
    · filter_upwards [heavy_support] with x hx
      exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  refine ⟨ha, hb, ?_⟩
  rw [a, b, ← integral_add heavy_exp_integrable heavy_mul_exp_integrable]
  have hbound : ∀ᵐ x ∂heavy, Real.exp (-x) + x * Real.exp (-x) ≤ 1 / 4 := by
    filter_upwards [heavy_support] with x hx
    have he := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ x)
    have he' : 4 * (1 + x) ≤ Real.exp x := by nlinarith [sq_nonneg (x - 9)]
    rw [Real.exp_neg]
    have hi := (div_le_div_iff_of_pos_right (Real.exp_pos x)).2 he'
    nlinarith [Real.exp_pos x, inv_mul_cancel₀ (Real.exp_ne_zero x)]
  simpa using integral_mono_ae (heavy_exp_integrable.add heavy_mul_exp_integrable)
    (integrable_const (1 / 4 : ℝ)) hbound

private noncomputable def A : ℝ := 1 - a - b * (1 - Real.exp (-1))
private noncomputable def p : ℝ := 1 / (2 * A)
private noncomputable def q : ℝ := p * b * Real.exp (-1)
private noncomputable def r : ℝ := 1 - p - q
private noncomputable def displacementLaw : Measure ℝ :=
  ENNReal.ofReal p • heavy + ENNReal.ofReal q • Measure.dirac (-1) +
    ENNReal.ofReal r • Measure.dirac 0

private lemma mixture_coefficients : 0 < p ∧ 0 < q ∧ 0 ≤ r ∧ p + q + r = 1 := by
  obtain ⟨ha, hb, hab⟩ := coefficient_bounds
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hA : 3 / 4 ≤ A := by dsimp [A]; nlinarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p ≤ 2 / 3 := by
    dsimp [p]
    apply (div_le_iff₀ (by linarith : 0 < 2 * A)).mpr
    linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : q ≤ p / 4 := by
    dsimp [q]
    have hbe : b * Real.exp (-1) ≤ 1 / 4 := by nlinarith
    nlinarith
  refine ⟨hp, hq, ?_, ?_⟩
  · dsimp [r]
    linarith
  · dsimp [r]
    ring

private instance displacementLaw_probability : IsProbabilityMeasure displacementLaw where
  measure_univ := by
    obtain ⟨hp, hq, hr, hsum⟩ := mixture_coefficients
    simp only [displacementLaw, add_apply, smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp.le hq.le, ← ENNReal.ofReal_add (by linarith) hr, hsum]
    norm_num

private lemma law_weighted_moment (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x)) displacementLaw := by
  apply integrable_add_measure.mpr
  refine ⟨integrable_add_measure.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (heavy_weighted_moment k).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma integral_displacementLaw (f : ℝ → ℝ) (hf : Integrable f heavy) :
    (∫ x, f x ∂displacementLaw) = p * (∫ x, f x ∂heavy) + q * f (-1) + r * f 0 := by
  obtain ⟨hp, hq, hr, _⟩ := mixture_coefficients
  have hi : Integrable f (ENNReal.ofReal p • heavy) := hf.smul_measure ENNReal.ofReal_ne_top
  have hj : Integrable f (ENNReal.ofReal q • Measure.dirac (-1)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hk : Integrable f (ENNReal.ofReal r • Measure.dirac 0) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [displacementLaw, integral_add_measure (integrable_add_measure.mpr ⟨hi, hj⟩) hk,
    integral_add_measure hi hj]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hr]

private noncomputable def spinalLaw : Measure ℝ :=
  displacementLaw.withDensity (fun x => ENNReal.ofReal (2 * Real.exp (-x)))

private lemma spinal_moment (k : ℕ) : Integrable (fun x : ℝ => x ^ k) spinalLaw := by
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all displacementLaw (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp (-_)), smul_eq_mul]
  convert (law_weighted_moment k).const_mul 2 using 1
  funext x
  ring

private lemma integral_spinal_moment (k : ℕ) :
    (∫ x, x ^ k ∂spinalLaw) = 2 * (∫ x, x ^ k * Real.exp (-x) ∂displacementLaw) := by
  rw [spinalLaw, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all displacementLaw (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp (-_)), smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

private lemma q_exp : q * Real.exp 1 = p * b := by
  rw [q, mul_assoc, ← Real.exp_add]
  norm_num

private lemma boundary_identity : p * a + q * Real.exp 1 + r = 1 / 2 := by
  have hA : A ≠ 0 := by
    obtain ⟨hp, _, _, _⟩ := mixture_coefficients
    intro h
    simp [p, h] at hp
  have hpA : p * A = 1 / 2 := by
    dsimp [p]
    field_simp
  rw [q_exp]
  dsimp [r, q]
  dsimp [A] at hpA
  nlinarith

private instance spinalLaw_probability : IsProbabilityMeasure spinalLaw where
  measure_univ := by
    have hi : Integrable (fun x : ℝ => Real.exp (-x)) displacementLaw := by
      simpa using law_weighted_moment 0
    have hvalue : (∫ x, Real.exp (-x) ∂displacementLaw) = 1 / 2 := by
      rw [integral_displacementLaw _ heavy_exp_integrable]
      simpa only [neg_neg, neg_zero, Real.exp_zero, mul_one, a] using boundary_identity
    rw [spinalLaw, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul 2)
      (ae_of_all _ (fun _ => by positivity)), integral_const_mul, hvalue]
    norm_num

private lemma spinal_centered : (∫ x, x ∂spinalLaw) = 0 := by
  have he := integral_spinal_moment 1
  simp only [pow_one] at he
  rw [he, integral_displacementLaw _ heavy_mul_exp_integrable]
  simp only [neg_neg, neg_zero, Real.exp_zero, zero_mul, mul_zero, add_zero]
  change 2 * (p * b + q * (-1 * Real.exp 1)) = 0
  nlinarith [q_exp]

private lemma spinal_variance_pos : 0 < ∫ x, x ^ 2 ∂spinalLaw := by
  obtain ⟨hp, hq, _, _⟩ := mixture_coefficients
  rw [integral_spinal_moment, integral_displacementLaw _ (heavy_weighted_moment 2)]
  have hc : 0 ≤ ∫ x, x ^ 2 * Real.exp (-x) ∂heavy :=
    integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  have he : 0 < Real.exp 1 := Real.exp_pos _
  norm_num only [neg_neg, neg_zero, Real.exp_zero, neg_pow, one_pow, zero_pow,
    one_mul, zero_mul, mul_zero, add_zero]
  positivity

private lemma displacement_not_integrable :
    ¬ Integrable (fun x : ℝ => max x 0) displacementLaw := by
  intro h
  have hheavy := (integrable_add_measure.mp (integrable_add_measure.mp h).1).1
  exact heavy_not_integrable ((integrable_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr mixture_coefficients.1))
    ENNReal.ofReal_ne_top).mp hheavy)

/-- A weak reproductive tail does not supply a first moment for the original
leftmost child, even with boundary normalization and positive finite spinal
variance. Both children are present and occupy the same position. -/
theorem exists_boundaryLaw_spinalWeightTail_not_integrable_leftmost :
    ∃ μ : Measure (Step (Fin 2) ℝ), IsProbabilityMeasure μ ∧
      HasBoundaryNormalization realPotential μ ∧ μ nonemptySupport = 1 ∧
      (∀ᵐ ξ ∂μ, (∀ i : Fin 2, survive ξ i) ∧ ∀ i, value' ξ i = value' ξ 0) ∧
      HasSpinalWeightTail realPotential μ ∧
      (∃ σ : ℝ, 0 < σ ∧ IsCenteredSecondMoment
        (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2) ∧
        Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw realPotential (-1) μ)) ∧
      ¬ Integrable (fun ξ => max (value' ξ 0) 0) μ := by
  let F : ℝ → Step (Fin 2) ℝ := fun x _ => some x
  let μ := displacementLaw.map F
  have hF : Measurable F := Measurable.of_eval (fun _ => measurable_option_some)
  have hscalar : tiltedPotentialLaw realPotential (-1) μ = spinalLaw := by
    change tiltedPotentialLaw realPotential (-1)
      (displacementLaw.map (fun x : ℝ => fun _ : Fin 2 => some x)) =
      displacementLaw.withDensity (fun x => ENNReal.ofReal (2 * Real.exp (-x)))
    simpa only [Nat.cast_ofNat, neg_one_mul] using
      tiltedPotentialLaw_map_replicated displacementLaw 2 (-1)
  have hboundary : HasBoundaryNormalization realPotential μ := by
    have h := tiltedPotentialLaw_apply_univ realPotential (-1) μ
    rw [hscalar, measure_univ] at h
    exact h.symm
  refine ⟨μ, inferInstance, hboundary, ?_, ?_, hasSpinalWeightTail_map_replicated _ (by norm_num),
    ?_, ?_⟩
  · rw [Measure.map_apply hF nonemptySupport_measurable]
    have he : F ⁻¹' nonemptySupport = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact ⟨0, x, rfl⟩
    rw [he, measure_univ]
  · apply (ae_map_iff hF.aemeasurable _).mpr
    · exact ae_of_all _ (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩)
    · convert (MeasurableSet.iInter fun i : Fin 2 => survive_measurableSet (X := ℝ) i).inter
        (MeasurableSet.iInter fun i : Fin 2 => measurableSet_eq_fun
          (value'_measurable (X := ℝ) i) (value'_measurable (0 : Fin 2))) using 1
      ext ξ
      simp
  · let v := ∫ x, x ^ 2 ∂spinalLaw
    have hv : 0 < v := spinal_variance_pos
    refine ⟨Real.sqrt v, Real.sqrt_pos.mpr hv, ?_⟩
    rw [hscalar]
    exact ⟨⟨spinal_centered, (Real.sq_sqrt hv.le).symm⟩, spinal_moment 2⟩
  · intro h
    have hi := h.comp_measurable hF
    exact displacement_not_integrable hi

end ProbabilityTheory.BranchingRandomWalk.Examples
