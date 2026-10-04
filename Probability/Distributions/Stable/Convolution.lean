/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import MeasureTheory.Measure.Convolution.Power

/-!
# Convolution of strictly stable laws

The weighted-copy definition of strict stability directly identifies
convolution of two scaled copies.  This is the measure-level starting point
for the convolution semigroup and infinite divisibility.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure

/-- Two scaled independent copies have the strictly stable scale. -/
theorem IsStrictlyAlphaStable.conv_scaled
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (μ.map fun x => a * x) ∗ (μ.map fun x => b * x) =
      μ.map fun x => alphaStableScale α a b * x := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  let f : ℝ → ℝ := fun x => a * x
  let g : ℝ → ℝ := fun x => b * x
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hprod :
      (μ.map fun x => a * x) ∗ (μ.map fun x => b * x) =
        (μ.prod μ).map (weightedSum a b) := by
    change (μ.map f) ∗ (μ.map g) = (μ.prod μ).map (weightedSum a b)
    rw [Measure.conv, Measure.map_prod_map μ μ hf hg]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hprod]
  exact h.2.2.2.2 a b ha hb

/-- The one-time law at positive time `t`. -/
noncomputable def stableTimeLaw (α : ℝ) (μ : Measure ℝ) (t : ℝ) : Measure ℝ :=
  μ.map fun x => t ^ (1 / α) * x

@[simp] theorem IsStrictlyAlphaStable.stableTimeLaw_zero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    stableTimeLaw α μ 0 = Measure.dirac 0 := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hscale : (0 : ℝ) ^ (1 / α) = 0 :=
    Real.zero_rpow (one_div_pos.mpr h.1).ne'
  simp only [stableTimeLaw, hscale, zero_mul]
  rw [Measure.map_const, measure_univ, one_smul]

@[simp] theorem IsStrictlyAlphaStable.stableTimeLaw_one
    {α : ℝ} {μ : Measure ℝ} (_h : IsStrictlyAlphaStable α μ) :
    stableTimeLaw α μ 1 = μ := by
  simp [stableTimeLaw]

/-- Positive-time strictly stable laws form a convolution semigroup. -/
theorem IsStrictlyAlphaStable.stableTimeLaw_conv
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    stableTimeLaw α μ s ∗ stableTimeLaw α μ t =
      stableTimeLaw α μ (s + t) := by
  have hα : α ≠ 0 := h.1.ne'
  have hscale_s : (s ^ (1 / α)) ^ α = s := by
    rw [← Real.rpow_mul hs.le, one_div_mul_cancel hα, Real.rpow_one]
  have hscale_t : (t ^ (1 / α)) ^ α = t := by
    rw [← Real.rpow_mul ht.le, one_div_mul_cancel hα, Real.rpow_one]
  have hspos : 0 < s ^ (1 / α) := Real.rpow_pos_of_pos hs _
  have htpos : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
  rw [stableTimeLaw, stableTimeLaw,
    h.conv_scaled hspos htpos]
  change μ.map (fun x =>
    ((s ^ (1 / α)) ^ α + (t ^ (1 / α)) ^ α) ^ (1 / α) * x) =
      μ.map (fun x => (s + t) ^ (1 / α) * x)
  rw [hscale_s, hscale_t]

/-- The semigroup law also includes the point mass at time zero. -/
theorem IsStrictlyAlphaStable.stableTimeLaw_conv_nonneg
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    stableTimeLaw α μ s ∗ stableTimeLaw α μ t =
      stableTimeLaw α μ (s + t) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  rcases hs.eq_or_lt with rfl | hspos
  · have : IsProbabilityMeasure (stableTimeLaw α μ t) := by
      unfold stableTimeLaw
      infer_instance
    simp [h.stableTimeLaw_zero]
  rcases ht.eq_or_lt with rfl | htpos
  · have : IsProbabilityMeasure (stableTimeLaw α μ s) := by
      unfold stableTimeLaw
      infer_instance
    simp [h.stableTimeLaw_zero]
  exact h.stableTimeLaw_conv hspos htpos

/-- Every strictly stable law has an explicit convolution root at each
positive integer order: the law at time `1 / n`. -/
theorem IsStrictlyAlphaStable.exists_convPower_root
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (n : ℕ) (hn : 0 < n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ μ = ν.convPower n := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let ν := stableTimeLaw α μ (1 / (n : ℝ))
  have hroot : ∀ k : ℕ,
      stableTimeLaw α μ ((k : ℝ) / (n : ℝ)) = ν.convPower k := by
    intro k
    induction k with
    | zero =>
        simpa [ν] using h.stableTimeLaw_zero
    | succ k ih =>
        have htime : ((k + 1 : ℕ) : ℝ) / (n : ℝ) =
            1 / (n : ℝ) + (k : ℝ) / (n : ℝ) := by
          push_cast
          ring
        rw [htime, ← h.stableTimeLaw_conv_nonneg (by positivity) (by positivity),
          ih, Measure.convPower_succ]
  refine ⟨ν, ?_, ?_⟩
  · dsimp [ν, stableTimeLaw]
    infer_instance
  · have hnn : (n : ℝ) / (n : ℝ) = 1 := div_self hnreal
    simpa [hnn, h.stableTimeLaw_one] using hroot n

/-- Integer-time stable laws are convolution powers of the unit-time law. -/
theorem IsStrictlyAlphaStable.stableTimeLaw_nat
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (n : ℕ) :
    stableTimeLaw α μ n = μ.convPower n := by
  induction n with
  | zero =>
      simpa using h.stableTimeLaw_zero
  | succ n ih =>
      have htime : ((n + 1 : ℕ) : ℝ) = 1 + (n : ℝ) := by push_cast; ring
      rw [htime, ← h.stableTimeLaw_conv_nonneg (by positivity) (by positivity),
        h.stableTimeLaw_one, ih, Measure.convPower_succ]

end ProbabilityTheory

end
