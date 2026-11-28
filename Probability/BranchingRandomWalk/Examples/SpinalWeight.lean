/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Replicated
public import Probability.Distributions.Moments.Real
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Binary reproduction with weak spinal tails and infinite cross weight

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Examples.exists_boundaryLaw_spinalWeightTail_not_finiteCrossWeight`:
  there is a boundary-normalized nonempty binary law with centered spinal
  variance `σ²>0`, the weak reproductive tail and finite positive leftmost
  first moment, but `∫C dμ=∞`.

The constructive strictness theorem uses the canonical
geometric measures and the existing family/child bias. Every child in a family
has the same displacement `(2-G) log 2`, where the original law of `G` is
geometric with success probability `2/3`. The spinal law has success
probability `1/3`. This example separates finite cross weight from the
reproductive condition (1.9) of B. Mallein, *N-branching random walk with
α-stable spine*, Theorem 1.1, arXiv:1503.03762v2. Both children are present,
the spinal mean is zero, and the relative reproductive mark is `log 2`.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Examples
open MeasureTheory Combinatorics.Branching Spine Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

private noncomputable def displacement (n : ℕ) : ℝ := (2 - (n : ℝ)) * Real.log 2
private noncomputable def family (n : ℕ) : Step (Fin 2) ℝ := fun _ => some (displacement n)
private noncomputable def rawParameter : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩
private noncomputable def spinalParameter : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩
private noncomputable def familyLaw : Measure (Step (Fin 2) ℝ) :=
  (geometricMeasure rawParameter).map family

private lemma measurable_family : Measurable family := measurable_of_countable _
private lemma measurable_displacement : Measurable displacement := measurable_of_countable _

private lemma exp_neg_displacement (n : ℕ) :
    Real.exp (-displacement n) = (2 : ℝ) ^ n / 4 := by
  rw [show -displacement n = (n : ℝ) * Real.log 2 - (2 : ℕ) * Real.log 2 by
    dsimp [displacement]; ring, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private lemma weight_identity (n : ℕ) :
    ((1 / 3 : ℝ) ^ n * (2 / 3)) * (2 * Real.exp (-displacement n)) =
      (2 / 3 : ℝ) ^ n * (1 / 3) := by
  rw [exp_neg_displacement]
  calc
    _ = ((1 / 3 : ℝ) ^ n * (2 : ℝ) ^ n) / 3 := by ring
    _ = ((1 / 3 : ℝ) * 2) ^ n / 3 := by rw [mul_pow]
    _ = _ := by norm_num; ring

private lemma scalar_law : tiltedPotentialLaw realPotential (-1) familyLaw =
    (geometricMeasure spinalParameter).map displacement := by
  have hm : Measurable (fun x : ℝ => fun _ : Fin 2 => some x) :=
    Measurable.of_eval (fun _ => measurable_option_some)
  have he : familyLaw = ((geometricMeasure rawParameter).map displacement).map
      (fun x : ℝ => fun _ : Fin 2 => some x) := by
    rw [Measure.map_map hm measurable_displacement]
    rfl
  rw [he, tiltedPotentialLaw_map_replicated]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf,
    lintegral_map (by fun_prop) measurable_displacement,
    lintegral_map hf measurable_displacement,
    geometricMeasure_eq (by exact ne_of_gt (show (0 : unitInterval) < rawParameter from
      by change (0 : ℝ) < 2 / 3; norm_num) : rawParameter ≠ 0),
    geometricMeasure_eq (by exact ne_of_gt (show (0 : unitInterval) < spinalParameter from
      by change (0 : ℝ) < 1 / 3; norm_num) : spinalParameter ≠ 0),
    lintegral_sum_measure, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  norm_num only [rawParameter, spinalParameter, Subtype.coe_mk, Nat.cast_ofNat, neg_one_mul,
    Pi.mul_apply, Function.comp_def]
  change ENNReal.ofReal ((1 / 3 : ℝ) ^ n * (2 / 3)) *
    (ENNReal.ofReal (2 * Real.exp (-displacement n)) * f (displacement n)) =
      ENNReal.ofReal ((2 / 3 : ℝ) ^ n * (1 / 3)) * f (displacement n)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), weight_identity]

private lemma boundary : HasBoundaryNormalization realPotential familyLaw := by
  have hprob : IsProbabilityMeasure (tiltedPotentialLaw realPotential (-1) familyLaw) := by
    rw [scalar_law]
    infer_instance
  have h := tiltedPotentialLaw_apply_univ realPotential (-1) familyLaw
  rw [measure_univ] at h
  exact h.symm

private instance familyLaw_probability : IsProbabilityMeasure familyLaw := by
  unfold familyLaw
  infer_instance

private lemma weak_tail : HasSpinalWeightTail realPotential familyLaw := by
  have hm : Measurable (fun x : ℝ => fun _ : Fin 2 => some x) :=
    Measurable.of_eval (fun _ => measurable_option_some)
  have he : familyLaw = ((geometricMeasure rawParameter).map displacement).map
      (fun x : ℝ => fun _ : Fin 2 => some x) := by
    rw [Measure.map_map hm measurable_displacement]
    rfl
  rw [he]
  exact hasSpinalWeightTail_map_replicated _ (by norm_num)

private lemma cross_weight : ¬ HasFiniteCrossWeight realPotential familyLaw := by
  have hfamily (n : ℕ) : crossPotentialWeight realPotential (-1) (family n) =
      ENNReal.ofReal (2 * (Real.exp (-displacement n)) ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_pow (Real.exp_nonneg _), ENNReal.ofReal_ofNat]
    simp [crossPotentialWeight, tsum_fintype, Fin.sum_univ_two,
      realizedPotentialWeight, family, survive, Step.potentialValue',
      Step.potentialAt?, realPotential, pow_two, two_mul]
  unfold HasFiniteCrossWeight
  rw [familyLaw, lintegral_map (crossPotentialWeight_measurable realPotential (-1)) measurable_family,
    geometricMeasure_eq (by exact ne_of_gt (show (0 : unitInterval) < rawParameter from
      by change (0 : ℝ) < 2 / 3; norm_num) : rawParameter ≠ 0), lintegral_sum_measure]
  have hlow : (∑' _ : ℕ, ENNReal.ofReal (1 / 12 : ℝ)) ≤
      ∑' n : ℕ, ∫⁻ ξ, crossPotentialWeight realPotential (-1) (family ξ)
        ∂(ENNReal.ofReal ((1 - (rawParameter : ℝ)) ^ n * rawParameter) • Measure.dirac n) := by
    apply tsum_le_tsum
    intro n
    change ENNReal.ofReal (1 / 12 : ℝ) ≤ ∫⁻ ξ,
      crossPotentialWeight realPotential (-1) (family ξ)
        ∂(ENNReal.ofReal ((1 - (rawParameter : ℝ)) ^ n * rawParameter) • Measure.dirac n)
    rw [lintegral_smul_measure, lintegral_dirac, hfamily, exp_neg_displacement]
    norm_num only [rawParameter, Subtype.coe_mk]
    change ENNReal.ofReal (1 / 12 : ℝ) ≤ ENNReal.ofReal ((1 / 3 : ℝ) ^ n * (2 / 3)) *
      ENNReal.ofReal (2 * ((2 : ℝ) ^ n / 4) ^ 2)
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have heq : ((1 / 3 : ℝ) ^ n * (2 / 3)) * (2 * ((2 : ℝ) ^ n / 4) ^ 2) =
        (1 / 12 : ℝ) * (4 / 3 : ℝ) ^ n := by
      have hsq : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      simp_rw [div_pow, hsq, one_pow]
      ring
    rw [heq]
    linarith
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num : ENNReal.ofReal (1 / 12 : ℝ) ≠ 0)] at hlow
  exact not_not.mpr (top_le_iff.mp hlow)

private lemma centered_variance : IsCenteredSecondMoment
    (tiltedPotentialLaw realPotential (-1) familyLaw) (6 * (Real.log 2) ^ 2) := by
  have hp : spinalParameter ≠ 0 := ne_of_gt (show (0 : unitInterval) < spinalParameter from
    by change (0 : ℝ) < 1 / 3; norm_num)
  have h0 : HasSum (fun n : ℕ => (2 / 3 : ℝ) ^ n) 3 := by
    convert hasSum_geometric_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num) using 1; norm_num
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (2 / 3 : ℝ) ^ n) 6 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (r := (2 / 3 : ℝ)) (by norm_num) using 1; norm_num
  have h2 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) 30 := by
    convert hasSum_sq_mul_geometric_of_norm_lt_one (r := (2 / 3 : ℝ)) (by norm_num) using 1; norm_num
  rw [scalar_law]
  constructor
  · rw [integral_map (f := fun x : ℝ => x) measurable_displacement.aemeasurable measurable_id.aestronglyMeasurable,
      integral_geometricMeasure hp]
    have h := (h0.mul_left (2 * Real.log 2 / 3)).sub (h1.mul_left (Real.log 2 / 3))
    have he : (fun n : ℕ => ((1 - (spinalParameter : ℝ)) ^ n * spinalParameter) • displacement n) =
        fun n : ℕ => (2 * Real.log 2 / 3) * (2 / 3 : ℝ) ^ n -
          (Real.log 2 / 3) * ((n : ℝ) * (2 / 3 : ℝ) ^ n) := by
      funext n
      norm_num [spinalParameter, displacement, smul_eq_mul]
      ring
    rw [he, h.tsum_eq]
    ring
  · rw [integral_map (f := fun x : ℝ => x ^ 2) measurable_displacement.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable,
      integral_geometricMeasure hp]
    have h := ((h0.mul_left (4 * (Real.log 2) ^ 2 / 3)).sub
      (h1.mul_left (4 * (Real.log 2) ^ 2 / 3))).add (h2.mul_left ((Real.log 2) ^ 2 / 3))
    have he : (fun n : ℕ => ((1 - (spinalParameter : ℝ)) ^ n * spinalParameter) • displacement n ^ 2) =
        fun n : ℕ => (4 * (Real.log 2) ^ 2 / 3) * (2 / 3 : ℝ) ^ n -
          (4 * (Real.log 2) ^ 2 / 3) * ((n : ℝ) * (2 / 3 : ℝ) ^ n) +
          ((Real.log 2) ^ 2 / 3) * ((n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) := by
      funext n
      norm_num [spinalParameter, displacement, smul_eq_mul]
      ring
    rw [he, h.tsum_eq]
    ring

private lemma nonempty : familyLaw nonemptySupport = 1 := by
  rw [familyLaw, Measure.map_apply measurable_family nonemptySupport_measurable]
  have he : family ⁻¹' nonemptySupport = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    exact ⟨0, displacement n, rfl⟩
  rw [he, measure_univ]

private lemma binary_shared_displacement : familyLaw {ξ |
    (∀ i, survive ξ i) ∧ ∀ i, value' ξ i = value' ξ 0} = 1 := by
  have hm : MeasurableSet {ξ : Step (Fin 2) ℝ |
      (∀ i, survive ξ i) ∧ ∀ i, value' ξ i = value' ξ 0} := by
    convert (MeasurableSet.iInter fun i : Fin 2 => survive_measurableSet (X := ℝ) i).inter
      (MeasurableSet.iInter fun i : Fin 2 => measurableSet_eq_fun
        (value'_measurable (X := ℝ) i) (value'_measurable (0 : Fin 2))) using 1
    ext ξ
    simp
  rw [familyLaw, Measure.map_apply measurable_family hm]
  have he : family ⁻¹' {ξ | (∀ i, survive ξ i) ∧ ∀ i, value' ξ i = value' ξ 0} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    exact ⟨fun _ => ⟨displacement n, rfl⟩, fun _ => rfl⟩
  rw [he, measure_univ]

private lemma positive_first_moment :
    Integrable (fun ξ : Step (Fin 2) ℝ => max (value' ξ 0) 0) familyLaw := by
  have hraw : ∀ᵐ ξ ∂familyLaw, ξ ∈ Set.range family :=
    ae_map_mem_range (Set.countable_range family).measurableSet measurable_family.aemeasurable
  refine (integrable_const (2 * Real.log 2)).mono'
    ((value'_measurable (0 : Fin 2)).max measurable_const).aestronglyMeasurable ?_
  filter_upwards [hraw] with ξ hξ
  obtain ⟨n, rfl⟩ := hξ
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · simp only [value', family, Option.getD_some, displacement]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  · positivity

/-- A concrete binary law witnesses strictness of the weak reproductive
condition within the boundary-normalized, centered finite-variance setting.
The child displacement is bounded above, so its positive first moment is
finite. The two siblings share their displacement, and the spinal mark is
constant even though the original cross-child expectation is infinite. -/
theorem exists_boundaryLaw_spinalWeightTail_not_finiteCrossWeight :
    ∃ μ : Measure (Step (Fin 2) ℝ), IsProbabilityMeasure μ ∧
      HasBoundaryNormalization realPotential μ ∧ μ nonemptySupport = 1 ∧
      μ {ξ | (∀ i, survive ξ i) ∧ ∀ i, value' ξ i = value' ξ 0} = 1 ∧
      HasSpinalWeightTail realPotential μ ∧
      Integrable (fun ξ => max (value' ξ 0) 0) μ ∧
      (∃ σ : ℝ, 0 < σ ∧ IsCenteredSecondMoment
        (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2)) ∧
      ¬ HasFiniteCrossWeight realPotential μ := by
  refine ⟨familyLaw, inferInstance, boundary, nonempty, binary_shared_displacement, weak_tail,
    positive_first_moment, ?_, cross_weight⟩
  refine ⟨Real.sqrt 6 * Real.log 2, mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.log_pos (by norm_num)), ?_⟩
  convert centered_variance using 1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

end ProbabilityTheory.BranchingRandomWalk.Examples
