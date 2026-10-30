/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Levy.Khintchine
import Probability.Distributions.Stable.Operations.Convolution
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Representation
import MeasureTheory.Measure.CharacteristicFunction.Convolution
import Analysis.FunctionalEquation.NNReal
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Scaling of the stable characteristic exponent

The integer scaling identity follows directly from the stable convolution
semigroup and uniqueness of a continuous logarithm. It is a first step toward
identifying the Lévy measure of a strictly stable law.

## Public declarations

Write `ψ = T.exponent` for a Lévy--Khintchine triple `T` representing `μ`.

* `IsStrictlyAlphaStable.exponent_nat`:
  `ψ((n : ℝ)^(1/α) ξ) = (n : ℂ) ψ(ξ)` for every natural `n`.
* `IsStrictlyAlphaStable.exponent_scaled_add`:
  `ψ(a * ξ) + ψ(b * ξ) = ψ(alphaStableScale α a b * ξ)` for `a,b > 0`.
* `IsStrictlyAlphaStable.exponent_time_add`:
  `ψ(s^(1/α) * ξ) + ψ(t^(1/α) * ξ) = ψ((s+t)^(1/α) * ξ)` for `s,t > 0`.
* `IsStrictlyAlphaStable.exponent_time` gives
  `ψ(t^(1/α) * ξ) = (t : ℂ) * ψ(ξ)` for `t ≥ 0`.
* `IsStrictlyAlphaStable.exponent_scale` gives
  `ψ(a * ξ) = ((a^α : ℝ) : ℂ) * ψ(ξ)` for `a > 0`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

/-- At integer scale the Lévy–Khintchine exponent of a strictly stable law
is homogeneous with exponent `α`. -/
theorem IsStrictlyAlphaStable.exponent_nat
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (n : ℕ) (ξ : ℝ) :
    T.exponent ((n : ℝ) ^ (1 / α) * ξ) =
      (n : ℂ) * T.exponent ξ := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  let r : ℝ := (n : ℝ) ^ (1 / α)
  have heq : (fun x : ℝ => T.exponent (r * x)) =
      (fun x : ℝ => (n : ℂ) * T.exponent x) := by
    have hcomp :
        (fun x : ℝ =>
          (⟨Complex.exp (T.exponent (r * x)), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0})) =
        (fun x : ℝ =>
          (⟨Complex.exp ((n : ℂ) * T.exponent x), Complex.exp_ne_zero _⟩ :
            {z : ℂ // z ≠ 0})) := by
      funext x
      apply Subtype.ext
      calc
        Complex.exp (T.exponent (r * x)) = charFun μ (r * x) := (hT _).symm
        _ = charFun (stableTimeLaw α μ n) x := by
          rw [stableTimeLaw, charFun_map_mul]
        _ = charFun (μ.convPower n) x := by
          rw [h.stableTimeLaw_nat]
        _ = (charFun μ x) ^ n := Measure.charFun_convPower μ n x
        _ = Complex.exp ((n : ℂ) * T.exponent x) := by
          rw [hT, Complex.exp_nat_mul]
    exact Complex.isCoveringMap_exp.eq_of_comp_eq
      (T.exponent_continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul T.exponent_continuous) hcomp 0 (by simp)
  exact congrFun heq ξ

/-- The exponent satisfies the functional equation encoded by strict
stability, without choosing a closed form for the Lévy measure. -/
theorem IsStrictlyAlphaStable.exponent_scaled_add
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ξ : ℝ) :
    T.exponent (a * ξ) + T.exponent (b * ξ) =
      T.exponent (alphaStableScale α a b * ξ) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have heq : (fun x : ℝ => T.exponent (a * x) + T.exponent (b * x)) =
      (fun x : ℝ => T.exponent (alphaStableScale α a b * x)) := by
    have hcomp :
        (fun x : ℝ =>
          (⟨Complex.exp (T.exponent (a * x) + T.exponent (b * x)),
            Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0})) =
        (fun x : ℝ =>
          (⟨Complex.exp (T.exponent (alphaStableScale α a b * x)),
            Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0})) := by
      funext x
      have h_exp : Complex.exp (T.exponent (a * x) + T.exponent (b * x)) =
          Complex.exp (T.exponent (alphaStableScale α a b * x)) := by
        rw [Complex.exp_add, ← hT, ← hT]
        rw [← charFun_map_mul a x, ← charFun_map_mul b x]
        rw [← charFun_conv]
        rw [h.conv_scaled ha hb, charFun_map_mul, hT]
      exact Subtype.ext h_exp
    exact Complex.isCoveringMap_exp.eq_of_comp_eq
      ((T.exponent_continuous.comp (continuous_const.mul continuous_id)).add
        (T.exponent_continuous.comp (continuous_const.mul continuous_id)))
      (T.exponent_continuous.comp (continuous_const.mul continuous_id)) hcomp 0 (by simp)
  exact congrFun heq ξ

/-- In the time parameter, the exponent is additive on positive times. -/
theorem IsStrictlyAlphaStable.exponent_time_add
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (ξ : ℝ) :
    T.exponent (s ^ (1 / α) * ξ) +
      T.exponent (t ^ (1 / α) * ξ) =
        T.exponent ((s + t) ^ (1 / α) * ξ) := by
  have hα : α ≠ 0 := h.1.ne'
  have hs_pow : (s ^ (1 / α)) ^ α = s := by
    rw [← Real.rpow_mul hs.le, one_div_mul_cancel hα, Real.rpow_one]
  have ht_pow : (t ^ (1 / α)) ^ α = t := by
    rw [← Real.rpow_mul ht.le, one_div_mul_cancel hα, Real.rpow_one]
  have hs_pos : 0 < s ^ (1 / α) := Real.rpow_pos_of_pos hs _
  have ht_pos : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
  have hscale := h.exponent_scaled_add T hT hs_pos ht_pos ξ
  rw [alphaStableScale, hs_pow, ht_pow] at hscale
  exact hscale

/-- Continuous time scaling of the stable characteristic exponent. -/
theorem IsStrictlyAlphaStable.exponent_time
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    T.exponent (t ^ (1 / α) * ξ) = (t : ℂ) * T.exponent ξ := by
  let f : ℝ≥0 → ℂ := fun x => T.exponent ((x : ℝ) ^ (1 / α) * ξ)
  have hf : Continuous f := by
    exact T.exponent_continuous.comp
      ((Real.continuous_rpow_const (one_div_nonneg.mpr h.1.le)).comp
        NNReal.continuous_coe |>.mul continuous_const)
  have hfzero : f 0 = 0 := by
    change T.exponent (((0 : ℝ) ^ (1 / α)) * ξ) = 0
    rw [Real.zero_rpow (one_div_pos.mpr h.1).ne', zero_mul, T.exponent_zero]
  have hadd : ∀ x y : ℝ≥0, f (x + y) = f x + f y := by
    intro x y
    by_cases hx : x = 0
    · subst x
      simp only [zero_add, hfzero, zero_add]
    by_cases hy : y = 0
    · subst y
      simp only [add_zero, hfzero]
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hx)
    have hypos : 0 < (y : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hy)
    simpa only [f, NNReal.coe_add, eq_comm] using
      (h.exponent_time_add T hT hxpos hypos ξ)
  let fHom : ℝ≥0 →+ ℂ :=
    { toFun := f
      map_zero' := hfzero
      map_add' := hadd }
  have hlin := map_nnreal_smul fHom hf (Real.toNNReal t)
  have hlin' : f (Real.toNNReal t) = (Real.toNNReal t : ℝ) • f 1 := by
    simpa only [fHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddHom.coe_mk] using hlin
  simpa only [f, Real.coe_toNNReal t ht, Real.toNNReal_one, NNReal.coe_one, Real.one_rpow, one_mul,
    Complex.real_smul,
    smul_eq_mul] using hlin'

/-- The characteristic exponent is homogeneous at every positive spatial
scale. -/
theorem IsStrictlyAlphaStable.exponent_scale
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    T.exponent (a * ξ) = ((a ^ α : ℝ) : ℂ) * T.exponent ξ := by
  have hα : α ≠ 0 := h.1.ne'
  have hm : α * (1 / α) = 1 := by field_simp
  have hscale : (a ^ α) ^ (1 / α) = a := by
    rw [← Real.rpow_mul ha.le, hm, Real.rpow_one]
  have ht : 0 ≤ a ^ α := (Real.rpow_pos_of_pos ha _).le
  simpa only [hscale] using h.exponent_time T hT ht ξ

end ProbabilityTheory
