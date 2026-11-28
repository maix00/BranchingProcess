/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail
public import Probability.Distributions.Moments.Real
import MeasureTheory.Measure.Tails.Examples
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# A weak reproductive tail with infinite spinal mark second moment

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Examples.exists_boundaryLaw_spinalWeightTail_infinite_mark_secondMoment`:
  a nonempty law has `∫W dμ=1`, centered finite spinal variance `σ²>0`,
  finite raw positive leftmost first moment, and `x²μ̂{B>x}→0`, while
  `∫⁻B²dμ̂=∞`, where `B=log W+X` is the existing relative mark.

The construction uses families of `2^(2^n)` children at displacement zero,
with raw mass proportional to `2^(-2^n)`. Three single-child atoms at
`log 2`, `-log 2`, and zero calibrate the boundary and spinal mean.
The native joint family/child bias is used, with its existing relative mark.
This separates the weak condition (1.9) of B. Mallein,
*N-branching random walk with α-stable spine*, Theorem 1.1,
arXiv:1503.03762v2, from a finite reproductive-mark second moment.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Examples
open MeasureTheory Combinatorics.Branching Spine Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

private noncomputable def finiteFamily (K : ℕ) (x : ℝ) : Step ℕ ℝ :=
  fun i => if i < K then some x else none

private lemma prefix_sum (K : ℕ) (x : ℝ) (g : ℕ → ℝ≥0∞) (v : ℝ≥0∞)
    (hg : ∀ i < K, g i = v) :
    (∑' i : ℕ, realizedPotentialWeight realPotential (-1) (finiteFamily K x) i * g i) =
      ENNReal.ofReal ((K : ℝ) * Real.exp (-x)) * v := by
  rw [tsum_eq_sum (s := Finset.range K) (fun i hi => by
    have hi' : ¬ i < K := by simpa using hi
    simp [finiteFamily, realizedPotentialWeight, survive, hi'])]
  calc
    _ = ∑ i ∈ Finset.range K, ENNReal.ofReal (Real.exp (-x)) * v := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < K := Finset.mem_range.mp hi
      simp [finiteFamily, realizedPotentialWeight, survive, hi', Step.potentialValue',
        Step.potentialAt?, realPotential, hg i hi']
    _ = _ := by
      simp [ENNReal.ofReal_mul (Nat.cast_nonneg K), nsmul_eq_mul, mul_assoc]

private lemma prefix_weight (K : ℕ) (x : ℝ) :
    totalPotentialWeight realPotential (-1) (finiteFamily K x) =
      ENNReal.ofReal ((K : ℝ) * Real.exp (-x)) := by
  simpa only [totalPotentialWeight, mul_one] using prefix_sum K x (fun _ => 1) 1 (by simp)

private lemma prefix_mark {K : ℕ} (x : ℝ) {i : ℕ} (hi : i < K) :
    relativeSpinalWeight realPotential (finiteFamily K x, i) = Real.log K := by
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold relativeSpinalWeight logTotalPotentialWeight
  rw [prefix_weight, ENNReal.toReal_ofReal (by positivity),
    Real.log_mul hK.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp [finiteFamily, hi, Step.potentialValue', Step.potentialAt?, realPotential]

private def offspringNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n)
private noncomputable def largeFamily (n : ℕ) : Step ℕ ℝ := finiteFamily (offspringNumber n) 0
private noncomputable def coefficient (n : ℕ) : ℝ := (1 / 16) / offspringNumber n
private lemma offspringNumber_ge (n : ℕ) : 2 ≤ offspringNumber n := by
  exact Nat.le_pow (by positivity)
private lemma coefficient_bounds (n : ℕ) : 0 < coefficient n ∧ coefficient n ≤ 1 / 32 := by
  have hn : (2 : ℝ) ≤ offspringNumber n := by exact_mod_cast offspringNumber_ge n
  constructor
  · unfold coefficient
    positivity
  · unfold coefficient
    apply (div_le_iff₀ (by linarith : 0 < (offspringNumber n : ℝ))).mpr
    linarith

private lemma log_offspringNumber (n : ℕ) :
    Real.log (offspringNumber n : ℝ) = (2 : ℝ) ^ n * Real.log 2 := by
  simp [offspringNumber, Nat.cast_pow, Real.log_pow]

variable (ν : Measure ℕ) [IsProbabilityMeasure ν]

private noncomputable def δ : ℝ := ∫ n, coefficient n ∂ν
private noncomputable def t : ℝ := 2 * (1 / 16 - δ ν)
private noncomputable def z : ℝ := 1 - 1 / 16 - 2 * t ν
private noncomputable def raw : Measure (Step ℕ ℝ) :=
  (ν.withDensity (fun n => ENNReal.ofReal (coefficient n))).map largeFamily +
    ENNReal.ofReal (2 * t ν) • Measure.dirac (finiteFamily 1 (Real.log 2)) +
    ENNReal.ofReal (t ν / 2) • Measure.dirac (finiteFamily 1 (-Real.log 2)) +
    ENNReal.ofReal (z ν) • Measure.dirac (finiteFamily 1 0)

private lemma coefficient_integrable : Integrable coefficient ν := by
  exact (integrable_const (1 / 32 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun n => by
      rw [Real.norm_eq_abs, abs_of_pos (coefficient_bounds n).1]
      exact (coefficient_bounds n).2)

private lemma δ_bounds : 0 ≤ δ ν ∧ δ ν ≤ 1 / 32 := by
  refine ⟨integral_nonneg (fun n => (coefficient_bounds n).1.le), ?_⟩
  have hi := coefficient_integrable ν
  simpa only [δ, integral_const, probReal_univ, smul_eq_mul, one_mul] using integral_mono_ae hi (integrable_const (1 / 32 : ℝ))
    (ae_of_all _ (fun n => (coefficient_bounds n).2))

private lemma t_pos : 0 < t ν := by dsimp [t]; linarith [(δ_bounds ν).2]
private lemma z_nonneg : 0 ≤ z ν := by dsimp [z, t]; linarith [(δ_bounds ν).1]

private lemma density_mass :
    (ν.withDensity (fun n => ENNReal.ofReal (coefficient n))) Set.univ = ENNReal.ofReal (δ ν) := by
  have hi := coefficient_integrable ν
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun n => (coefficient_bounds n).1.le))).symm

private instance raw_probability : IsProbabilityMeasure (raw ν) where
  measure_univ := by
    have ht := t_pos ν
    have hz := z_nonneg ν
    have hδ := (δ_bounds ν).1
    simp only [raw, add_apply, smul_apply, Measure.map_apply_of_aemeasurable
      (measurable_of_countable largeFamily).aemeasurable MeasurableSet.univ,
      Set.preimage_univ, density_mass, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hδ (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hz]
    have he : δ ν + 2 * t ν + t ν / 2 + z ν = 1 := by dsimp [z, t]; ring
    rw [he]
    norm_num

omit [IsProbabilityMeasure ν] in
private lemma lintegral_raw (G : Step ℕ ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ ξ, G ξ ∂raw ν) =
      (∫⁻ n, ENNReal.ofReal (coefficient n) * G (largeFamily n) ∂ν) +
      ENNReal.ofReal (2 * t ν) * G (finiteFamily 1 (Real.log 2)) +
      ENNReal.ofReal (t ν / 2) * G (finiteFamily 1 (-Real.log 2)) +
      ENNReal.ofReal (z ν) * G (finiteFamily 1 0) := by
  rw [raw, lintegral_add_measure, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hG (measurable_of_countable _),
    lintegral_withDensity_eq_lintegral_mul ν (measurable_of_countable _) (by fun_prop)]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, Pi.mul_apply]

private lemma coefficient_cancel (n : ℕ) :
    ENNReal.ofReal (coefficient n) * ENNReal.ofReal (offspringNumber n : ℝ) =
      ENNReal.ofReal (1 / 16 : ℝ) := by
  rw [← ENNReal.ofReal_mul (coefficient_bounds n).1.le]
  congr 1
  exact div_mul_cancel₀ _ (by exact_mod_cast (by have := offspringNumber_ge n; omega : offspringNumber n ≠ 0))

private lemma prefix_scalar_test (K : ℕ) (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (∑' i : ℕ, realizedPotentialWeight realPotential (-1) (finiteFamily K x) i *
      f ((finiteFamily K x).potentialValue' realPotential i)) =
      ENNReal.ofReal ((K : ℝ) * Real.exp (-x)) * f x := by
  apply prefix_sum
  intro i hi
  simp [finiteFamily, hi, Step.potentialValue', Step.potentialAt?, realPotential]

private lemma prefix_mark_test (K : ℕ) (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (∑' i : ℕ, realizedPotentialWeight realPotential (-1) (finiteFamily K x) i *
      f (relativeSpinalWeight realPotential (finiteFamily K x, i))) =
      ENNReal.ofReal ((K : ℝ) * Real.exp (-x)) * f (Real.log K) := by
  apply prefix_sum
  intro i hi
  rw [prefix_mark x hi]

private lemma scalar_law : tiltedPotentialLaw realPotential (-1) (raw ν) =
    ENNReal.ofReal (1 / 16 + z ν) • Measure.dirac 0 +
      ENNReal.ofReal (t ν) • Measure.dirac (Real.log 2) +
      ENNReal.ofReal (t ν) • Measure.dirac (-Real.log 2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_tiltedPotentialLaw realPotential (-1) (raw ν) f hf]
  have hm : Measurable (fun ξ : Step ℕ ℝ => ∑' i : ℕ,
      realizedPotentialWeight realPotential (-1) ξ i * f (ξ.potentialValue' realPotential i)) := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable realPotential (-1) i).mul
      (hf.comp (Step.potentialValue'_measurable realPotential i))
  rw [lintegral_raw ν _ hm]
  simp only [largeFamily, prefix_scalar_test, neg_zero, Real.exp_zero, mul_one,
    ← mul_assoc, coefficient_cancel, lintegral_const, measure_univ, mul_one,
    Nat.cast_one, one_mul, neg_neg, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have ht := t_pos ν
  have hz := z_nonneg ν
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t ν),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ t ν / 2)]
  norm_num only [show 2 * t ν * (2 : ℝ)⁻¹ = t ν by ring,
    show t ν / 2 * 2 = t ν by ring]
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 16) hz, add_mul]
  norm_num
  rw [show 2 * t ν * (1 / 2 : ℝ) = t ν by ring]
  ring

private lemma mark_law :
    (tiltedFamilyChildLaw realPotential (-1) (raw ν)).map (relativeSpinalWeight realPotential) =
      ENNReal.ofReal (1 / 16 : ℝ) • ν.map (fun n => (2 : ℝ) ^ n * Real.log 2) +
      ENNReal.ofReal (15 / 16 : ℝ) • Measure.dirac 0 := by
  apply Measure.ext_of_lintegral
  intro f hf
  have ht := t_pos ν
  rw [lintegral_map hf (relativeSpinalWeight_measurable realPotential)]
  rw [lintegral_tiltedFamilyChildLaw realPotential (-1) (raw ν)
    (F := fun p => f (relativeSpinalWeight realPotential p))
    (hf.comp (relativeSpinalWeight_measurable realPotential))]
  have hm : Measurable (fun ξ : Step ℕ ℝ => ∑' i : ℕ,
      realizedPotentialWeight realPotential (-1) ξ i * f (relativeSpinalWeight realPotential (ξ, i))) := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable realPotential (-1) i).mul
      ((hf.comp (relativeSpinalWeight_measurable realPotential)).comp
        (measurable_id.prodMk measurable_const))
  rw [lintegral_raw ν _ hm]
  simp only [largeFamily, prefix_mark_test, log_offspringNumber, Real.log_one,
    Nat.cast_one, one_mul, neg_zero, Real.exp_zero, mul_one, ← mul_assoc, coefficient_cancel,
    neg_neg, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    lintegral_map hf (measurable_of_countable _)]
  rw [lintegral_const_mul _ (f := fun n : ℕ => f ((2 : ℝ) ^ n * Real.log 2))
    (hf.comp (measurable_of_countable _)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t ν),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ t ν / 2)]
  norm_num only [show 2 * t ν * (2 : ℝ)⁻¹ = t ν by ring,
    show t ν / 2 * 2 = t ν by ring]
  have he : t ν + t ν + z ν = (15 / 16 : ℝ) := by dsimp [z]; ring
  simp only [ENNReal.ofReal_one, mul_one]
  rw [show 2 * t ν * (1 / 2 : ℝ) = t ν by ring]
  rw [← he, ENNReal.ofReal_add (by linarith : 0 ≤ t ν + t ν) (z_nonneg ν),
    ENNReal.ofReal_add ht.le ht.le, add_mul, add_mul]
  ring

private lemma scalar_integrable (f : ℝ → ℝ) :
    Integrable f (tiltedPotentialLaw realPotential (-1) (raw ν)) := by
  rw [scalar_law]
  apply integrable_add_measure.mpr
  refine ⟨integrable_add_measure.mpr ⟨?_, ?_⟩, ?_⟩ <;>
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma scalar_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂tiltedPotentialLaw realPotential (-1) (raw ν)) =
      (1 / 16 + z ν) * f 0 + t ν * f (Real.log 2) + t ν * f (-Real.log 2) := by
  rw [scalar_law]
  have hs := scalar_integrable ν f
  rw [scalar_law] at hs
  obtain ⟨h01, hn⟩ := integrable_add_measure.mp hs
  obtain ⟨h0, hp⟩ := integrable_add_measure.mp h01
  rw [integral_add_measure (integrable_add_measure.mpr ⟨h0, hp⟩) hn,
    integral_add_measure h0 hp]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (t_pos ν).le,
    ENNReal.toReal_ofReal (by linarith [z_nonneg ν] : 0 ≤ 1 / 16 + z ν)]

private lemma boundary : HasBoundaryNormalization realPotential (raw ν) := by
  have hprob : IsProbabilityMeasure (tiltedPotentialLaw realPotential (-1) (raw ν)) := by
    constructor
    rw [scalar_law]
    simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith [z_nonneg ν]) (t_pos ν).le,
      ← ENNReal.ofReal_add (by linarith [z_nonneg ν, t_pos ν]) (t_pos ν).le]
    have he : 1 / 16 + z ν + t ν + t ν = 1 := by dsimp [z]; ring
    rw [he]
    norm_num
  have he := tiltedPotentialLaw_apply_univ realPotential (-1) (raw ν)
  rw [measure_univ] at he
  exact he.symm

private lemma scalar_centered : IsCenteredSecondMoment
    (tiltedPotentialLaw realPotential (-1) (raw ν)) (2 * t ν * (Real.log 2) ^ 2) := by
  constructor
  · rw [scalar_integral]
    ring
  · rw [scalar_integral]
    ring

omit [IsProbabilityMeasure ν] in
private lemma ae_raw (Q : Step ℕ ℝ → Prop) (hQ : MeasurableSet {ξ | Q ξ})
    (hlarge : ∀ n, Q (largeFamily n))
    (hp : Q (finiteFamily 1 (Real.log 2))) (hn : Q (finiteFamily 1 (-Real.log 2)))
    (hz : Q (finiteFamily 1 0)) : ∀ᵐ ξ ∂raw ν, Q ξ := by
  rw [raw, ae_add_measure_iff, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (ae_map_iff (measurable_of_countable largeFamily).aemeasurable hQ).mpr
      (ae_of_all _ hlarge)
  · exact Measure.ae_smul_measure ((ae_dirac_iff hQ).mpr hp) _
  · exact Measure.ae_smul_measure ((ae_dirac_iff hQ).mpr hn) _
  · exact Measure.ae_smul_measure ((ae_dirac_iff hQ).mpr hz) _

private lemma nonempty : raw ν nonemptySupport = 1 := by
  have hp : ∀ K : ℕ, 0 < K → ∀ x : ℝ, finiteFamily K x ∈ nonemptySupport := by
    intro K hK x
    exact ⟨0, x, by simp [finiteFamily, hK]⟩
  have he := ae_raw ν (fun ξ => ξ ∈ nonemptySupport) nonemptySupport_measurable
    (fun n => hp _ (by have := offspringNumber_ge n; omega) 0)
    (hp 1 (by norm_num) _) (hp 1 (by norm_num) _) (hp 1 (by norm_num) _)
  exact (mem_ae_iff_prob_eq_one nonemptySupport_measurable).mp he

private lemma leftmost_firstMoment : Integrable (fun ξ : Step ℕ ℝ => max (value' ξ 0) 0) (raw ν) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb : ∀ᵐ ξ ∂raw ν, max (value' ξ 0) 0 ≤ Real.log 2 := by
    apply ae_raw ν (fun ξ => max (value' ξ 0) 0 ≤ Real.log 2)
      (measurableSet_le ((value'_measurable (0 : ℕ)).max measurable_const) measurable_const)
    · intro n
      have hK : 0 < offspringNumber n := by have := offspringNumber_ge n; omega
      simpa [largeFamily, finiteFamily, value', hK] using hlog
    · simp [finiteFamily, value', max_eq_left hlog]
    · simpa [finiteFamily, value', max_eq_right (neg_nonpos.mpr hlog)] using hlog
    · simpa [finiteFamily, value'] using hlog
  refine (integrable_const (Real.log 2)).mono'
    ((value'_measurable (0 : ℕ)).max measurable_const).aestronglyMeasurable ?_
  filter_upwards [hb] with ξ hξ
  rwa [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]

omit [IsProbabilityMeasure ν] in
private lemma shared_displacement : ∀ᵐ ξ ∂raw ν,
    survive ξ 0 ∧ ∀ i, survive ξ i → value' ξ i = value' ξ 0 := by
  have hp (K : ℕ) (hK : 0 < K) (x : ℝ) : survive (finiteFamily K x) 0 ∧
      ∀ i, survive (finiteFamily K x) i → value' (finiteFamily K x) i = value' (finiteFamily K x) 0 := by
    refine ⟨⟨x, by simp [finiteFamily, hK]⟩, ?_⟩
    intro i hi
    have hi' : i < K := by
      by_contra h
      simp [finiteFamily, h, survive] at hi
    simp [finiteFamily, value', hi', hK]
  apply ae_raw ν _ _ (fun n => hp _ (by have := offspringNumber_ge n; omega) 0)
    (hp 1 (by norm_num) _) (hp 1 (by norm_num) _) (hp 1 (by norm_num) _)
  convert (survive_measurableSet (X := ℝ) (0 : ℕ)).inter
    (MeasurableSet.iInter fun i : ℕ => (survive_measurableSet (X := ℝ) i).compl.union
      (measurableSet_eq_fun (value'_measurable i) (value'_measurable (0 : ℕ)))) using 1
  ext ξ
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
    Set.mem_ofPred_eq, imp_iff_not_or]

private lemma mark_tail_probability {x : ℝ} (hx : 0 ≤ x) :
    (tiltedFamilyChildLaw realPotential (-1) (raw ν)).real
      {p | x < relativeSpinalWeight realPotential p} =
      (1 / 16 : ℝ) * ν.real {n | x < (2 : ℝ) ^ n * Real.log 2} := by
  have he := congrArg (fun μ : Measure ℝ => μ (Set.Ioi x)) (mark_law ν)
  rw [Measure.map_apply (relativeSpinalWeight_measurable realPotential) measurableSet_Ioi,
    add_apply, smul_apply, smul_apply,
    Measure.map_apply (measurable_of_countable _) measurableSet_Ioi,
    Measure.dirac_apply' _ measurableSet_Ioi] at he
  simp only [Set.indicator_apply, Set.mem_Ioi, not_lt.mpr hx, ↓reduceIte,
    smul_eq_mul, mul_zero, add_zero, Set.preimage] at he
  change (tiltedFamilyChildLaw realPotential (-1) (raw ν)
    {p | x < relativeSpinalWeight realPotential p}).toReal = _
  rw [he, ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  rfl

private lemma weak_mark_tail
    (htail : HasVanishingQuadraticTail ν (fun n => (2 : ℝ) ^ n)) :
    HasSpinalWeightTail realPotential (raw ν) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := htail.scale_threshold (inv_pos.mpr hlog)
  have hs' : HasVanishingQuadraticTail ν (fun n => (2 : ℝ) ^ n * Real.log 2) := by
    apply hs.congr
    intro x
    congr 2
    ext n
    change (Real.log 2)⁻¹ * x < (2 : ℝ) ^ n ↔ x < (2 : ℝ) ^ n * Real.log 2
    rw [show (Real.log 2)⁻¹ * x = x / Real.log 2 by ring, div_lt_iff₀ hlog]
  have he := hs'.const_mul (1 / 16 : ℝ)
  simp only [mul_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [mark_tail_probability ν hx]
  ring

private lemma infinite_mark_moment
    (hinf : (∫⁻ n, ENNReal.ofReal (((2 : ℝ) ^ n) ^ 2) ∂ν) = ∞) :
    (∫⁻ p, ENNReal.ofReal (relativeSpinalWeight realPotential p ^ 2)
      ∂tiltedFamilyChildLaw realPotential (-1) (raw ν)) = ∞ := by
  have hm := relativeSpinalWeight_measurable (ι := ℕ) realPotential
  rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ 2)) (by fun_prop) hm,
    mark_law, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac,
    lintegral_map (by fun_prop) (measurable_of_countable _)]
  have he : (fun n : ℕ => ENNReal.ofReal (((2 : ℝ) ^ n * Real.log 2) ^ 2)) =
      fun n => ENNReal.ofReal ((Real.log 2) ^ 2) * ENNReal.ofReal (((2 : ℝ) ^ n) ^ 2) := by
    funext n
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  rw [he, lintegral_const_mul _ (by fun_prop), hinf]
  have hl : ENNReal.ofReal ((Real.log 2) ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (Real.log_pos (by norm_num))))
  simp [hl]

/-- A nonempty boundary-normalized offspring law with finite positive centered
spinal variance and finite positive leftmost first moment can have a vanishing
quadratic reproductive tail and an infinite spinal reproductive-mark square.
All large families lie at displacement zero, so their marks do not increase
the spinal displacement variance. -/
theorem exists_boundaryLaw_spinalWeightTail_infinite_mark_secondMoment :
    ∃ μ : Measure (Step ℕ ℝ), IsProbabilityMeasure μ ∧
      HasBoundaryNormalization realPotential μ ∧ μ nonemptySupport = 1 ∧
      (∀ᵐ ξ ∂μ, survive ξ 0 ∧ ∀ i, survive ξ i → value' ξ i = value' ξ 0) ∧
      HasSpinalWeightTail realPotential μ ∧
      Integrable (fun ξ => max (value' ξ 0) 0) μ ∧
      (∃ σ : ℝ, 0 < σ ∧ IsCenteredSecondMoment
        (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2) ∧
        Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw realPotential (-1) μ)) ∧
      (∫⁻ p, ENNReal.ofReal (relativeSpinalWeight realPotential p ^ 2)
        ∂tiltedFamilyChildLaw realPotential (-1) μ) = ∞ := by
  obtain ⟨ν, hprob, htail, hinf⟩ :=
    MeasureTheory.exists_probabilityMeasure_nat_vanishingQuadraticTail_infinite_secondMoment
  have := hprob
  refine ⟨raw ν, inferInstance, boundary ν, nonempty ν, shared_displacement ν, weak_mark_tail ν htail,
    leftmost_firstMoment ν, ?_, infinite_mark_moment ν hinf⟩
  refine ⟨Real.sqrt (2 * t ν) * Real.log 2,
    mul_pos (Real.sqrt_pos.mpr (by linarith [t_pos ν])) (Real.log_pos (by norm_num)), ?_,
    scalar_integrable ν _⟩
  convert scalar_centered ν using 1
  rw [mul_pow, Real.sq_sqrt (by linarith [t_pos ν] : 0 ≤ 2 * t ν)]

end ProbabilityTheory.BranchingRandomWalk.Examples
