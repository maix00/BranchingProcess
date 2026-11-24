/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite products of countably weighted marked measures

## Public declarations

In `MeasureTheory.Measure`:

* `pi_sum_map_withDensity` expands the product of joint weighted measures:
  if `γᵢ = ∑ⱼ (μᵢ.withDensity wᵢⱼ).map (x ↦ (x,j))`, then
  `⊗ᵢ γᵢ = ∑_s ((⊗ᵢ μᵢ).withDensity (∏ᵢ wᵢ,sᵢ)).map (x ↦ (xᵢ,sᵢ))`.
* `lintegral_pi_sum_map_withDensity` gives the corresponding integral formula
  for every measurable nonnegative test of the entire vector of pairs.

The base measures are probabilities, the marked measures are finite, and
the mark type is countable. Weights can depend on both the base observation
and the mark. There is no independence assumption between them. These are
measure operations on finite products, without a tree or branching model.
Native product-measure uniqueness and independent-coordinate integration are
used; no additional product-measure definition is introduced.
-/

@[expose] public section
namespace MeasureTheory.Measure
open scoped ENNReal
open ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

private lemma tsum_fin_prod {J : Type*} (n : ℕ) (f : Fin n → J → ℝ≥0∞) :
    (∑' s : Fin n → J, ∏ i, f i (s i)) = ∏ i, ∑' j, f i j := by
  induction n with
  | zero => simp [tsum_fintype]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => J)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right]

private lemma lintegral_pi_prod {E : Type*} [MeasurableSpace E]
    {n : ℕ} (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  rw [← Measure.infinitePi_eq_pi]
  have hi := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : Fin n → E) => f i (x i))
    (iIndepFun_infinitePi (P := μ) (X := fun i x => f i x) hf) (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hi]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i), Measure.infinitePi_map_eval]

theorem pi_sum_map_withDensity {E J : Type*} [MeasurableSpace E]
    [MeasurableSpace J] [Countable J] {n : ℕ}
    (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (w : Fin n → J → E → ℝ≥0∞) (hw : ∀ i j, Measurable (w i j))
    [∀ i, IsFiniteMeasure (Measure.sum fun j =>
      ((μ i).withDensity (w i j)).map (fun x => (x, j)))] :
    (Measure.pi fun i => Measure.sum fun j =>
      ((μ i).withDensity (w i j)).map (fun x => (x, j))) =
      Measure.sum fun s : Fin n → J =>
        ((Measure.pi μ).withDensity (fun x => ∏ i, w i (s i) (x i))).map
          (fun x i => (x i, s i)) := by
  classical
  apply Measure.pi_eq
  intro A hA
  have hpair (s : Fin n → J) : Measurable
      (fun x : Fin n → E => fun i => (x i, s i)) := by fun_prop
  rw [Measure.sum_apply _ (.univ_pi hA)]
  have hslot (s : Fin n → J) :
      (((Measure.pi μ).withDensity (fun x => ∏ i, w i (s i) (x i))).map
        (fun x i => (x i, s i))) (Set.univ.pi A) =
      ∏ i, ∫⁻ x, w i (s i) x * (A i).indicator (fun _ => 1) (x, s i) ∂μ i := by
    rw [Measure.map_apply (hpair s) (.univ_pi hA), withDensity_apply _ ((MeasurableSet.univ_pi hA).preimage (hpair s)),
      ← lintegral_indicator ((MeasurableSet.univ_pi hA).preimage (hpair s))]
    have he (x : Fin n → E) :
        ((fun x i => (x i, s i)) ⁻¹' Set.univ.pi A).indicator
          (fun x => ∏ i, w i (s i) (x i)) x =
        ∏ i, w i (s i) (x i) * (A i).indicator (fun _ => 1) (x i, s i) := by
      classical
      by_cases hx : ∀ i, (x i, s i) ∈ A i
      · simp [Set.mem_pi, hx]
      · obtain ⟨i, hi⟩ := not_forall.mp hx
        have hp : (∏ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) (x i, s i)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
        simp [Set.mem_pi, hx, Finset.prod_mul_distrib, hp]
    simp_rw [he]
    exact lintegral_pi_prod μ _ (fun i => (hw i (s i)).mul
      (measurable_const.indicator ((hA i).preimage
        (show Measurable (fun x : E => (x, s i)) from by fun_prop))))
  simp_rw [hslot]
  rw [tsum_fin_prod n (fun i j =>
    ∫⁻ x, w i j x * (A i).indicator (fun _ => 1) (x, j) ∂μ i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.sum_apply _ (hA i)]
  apply tsum_congr
  intro j
  rw [Measure.map_apply (show Measurable (fun x : E => (x, j)) from by fun_prop) (hA i),
    withDensity_apply _ ((hA i).preimage (by fun_prop)),
    ← lintegral_indicator ((hA i).preimage (by fun_prop))]
  apply lintegral_congr
  intro x
  by_cases hx : (x, j) ∈ A i <;> simp [hx]

theorem lintegral_pi_sum_map_withDensity {E J : Type*} [MeasurableSpace E]
    [MeasurableSpace J] [Countable J] {n : ℕ}
    (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (w : Fin n → J → E → ℝ≥0∞) (hw : ∀ i j, Measurable (w i j))
    [∀ i, IsFiniteMeasure (Measure.sum fun j =>
      ((μ i).withDensity (w i j)).map (fun x => (x, j)))]
    {F : (Fin n → E × J) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂Measure.pi fun i => Measure.sum fun j =>
      ((μ i).withDensity (w i j)).map (fun x => (x, j))) =
      ∑' s : Fin n → J, ∫⁻ x, (∏ i, w i (s i) (x i)) *
        F (fun i => (x i, s i)) ∂Measure.pi μ := by
  rw [pi_sum_map_withDensity μ w hw, lintegral_sum_measure]
  apply tsum_congr
  intro s
  rw [lintegral_map hF (show Measurable (fun x : Fin n → E => fun i => (x i, s i)) from by fun_prop)]
  exact lintegral_withDensity_eq_lintegral_mul _
    (Finset.measurable_prod _ (fun i _ => (hw i (s i)).comp (measurable_pi_apply i)))
    (hF.comp (by fun_prop))

end MeasureTheory.Measure
