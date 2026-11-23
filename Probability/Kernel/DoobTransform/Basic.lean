/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.WithDensity

/-!
# Doob transforms of measurable kernels

## Public declarations

In `ProbabilityTheory.Kernel`:

* `doobTransform K h` is the native density kernel
  `K(x,dy) h(y)/h(x)` on an arbitrary measurable state space.
* `doobTransform_apply` identifies its measure at each state.
* `lintegral_doobTransform` states
  `∫ f dKʰ(x) = (∫ h(y) f(y) dK(x))/h(x)` for measurable nonnegative tests.
* `doobTransform_isMarkovKernel` proves normalization from
  `∫ h(y) dK(x) = h(x)` and `0 < h(x) < ∞`.
* `doobTransform_isProbabilityMeasure` gives the same normalization at a
  single eligible state, permitting zero weights elsewhere.
* `doobTransform_isSFiniteKernel` preserves s-finiteness when `0 < h(x) < ∞`.
* `doobTransform_one` identifies the constant-one specialization with `K`.
* `ae_doobTransform_weight_ne_zero` states that the transformed transition
  avoids zero-weight states. `ae_doobTransform_weight_ne_top` excludes
  infinite-weight states when `K h(x) < ∞`.

Zhan Shi, *Branching Random Walks*, Lecture Notes in Mathematics 2151
(Springer, 2015), Chapter 4, §4.2, (4.3)–(4.4),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf),
defines this transform for the transition killed outside a region. Here `K`
may be any s-finite kernel; killing is expressed by the input kernel. The
construction imposes no additive, order or standard-Borel state structure.
-/

@[expose] public section

namespace ProbabilityTheory.Kernel

open MeasureTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- The Doob transform is a density change of the original kernel. -/
noncomputable def doobTransform (K : Kernel S S) [IsSFiniteKernel K]
    (h : S → ℝ≥0∞) : Kernel S S :=
  K.withDensity (fun x y => h y / h x)

theorem doobTransform_apply (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h) (x : S) :
    doobTransform K h x = (K x).withDensity (fun y => h y / h x) := by
  apply Kernel.withDensity_apply
  fun_prop

/-- Integrating against the transformed kernel is normalized harmonic weighting. -/
theorem lintegral_doobTransform (K : Kernel S S) [IsSFiniteKernel K]
    {h f : S → ℝ≥0∞} (hh : Measurable h) (hf : Measurable f) (x : S) :
    (∫⁻ y, f y ∂doobTransform K h x) = (∫⁻ y, h y * f y ∂K x) / h x := by
  have hd : Measurable (Function.uncurry (fun x y => h y / h x)) := by fun_prop
  rw [doobTransform, Kernel.lintegral_withDensity K hd x hf]
  simp only [div_eq_mul_inv]
  calc
    (∫⁻ y, h y * (h x)⁻¹ * f y ∂K x) =
        ∫⁻ y, (h y * f y) * (h x)⁻¹ ∂K x := by
      apply lintegral_congr
      intro y
      ac_rfl
    _ = _ := lintegral_mul_const _ (hh.mul hf)

/-- Harmonicity normalizes the kernel at a single positive finite-weight state. -/
theorem doobTransform_isProbabilityMeasure (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h) (x : S)
    (hzero : h x ≠ 0) (htop : h x ≠ ∞)
    (harmonic : (∫⁻ y, h y ∂K x) = h x) :
    IsProbabilityMeasure (doobTransform K h x) := by
  constructor
  have hi := lintegral_doobTransform K hh measurable_const x (f := fun _ => 1)
  simpa only [lintegral_one, mul_one, harmonic, ENNReal.div_self hzero htop] using hi

/-- Harmonicity and finite positive weights make the Doob transform a probability kernel. -/
theorem doobTransform_isMarkovKernel (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞)
    (harmonic : ∀ x, (∫⁻ y, h y ∂K x) = h x) :
    IsMarkovKernel (doobTransform K h) where
  isProbabilityMeasure x :=
    doobTransform_isProbabilityMeasure K hh x (hzero x) (htop x) (harmonic x)

/-- Finite positive weights preserve s-finiteness of the native density kernel. -/
theorem doobTransform_isSFiniteKernel (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞) :
    IsSFiniteKernel (doobTransform K h) :=
  IsSFiniteKernel.withDensity K (fun x y => ENNReal.div_ne_top (htop y) (hzero x))

@[simp] theorem doobTransform_one (K : Kernel S S) [IsSFiniteKernel K] :
    doobTransform K (fun _ => 1) = K := by
  simp [doobTransform]

/-- The density transform assigns zero mass to zero-weight target states. -/
theorem ae_doobTransform_weight_ne_zero (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h) (x : S) :
    ∀ᵐ y ∂doobTransform K h x, h y ≠ 0 := by
  rw [doobTransform_apply K hh]
  apply (ae_withDensity_iff (hh.div_const (h x))).mpr
  exact Filter.Eventually.of_forall fun y hy hyzero => hy (by rw [hyzero]; exact ENNReal.zero_div)

/-- Finite harmonic mass makes infinite-weight targets null under the transform. -/
theorem ae_doobTransform_weight_ne_top (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h) (x : S)
    (hfinite : (∫⁻ y, h y ∂K x) ≠ ∞) :
    ∀ᵐ y ∂doobTransform K h x, h y ≠ ∞ := by
  rw [doobTransform_apply K hh]
  apply (MeasureTheory.withDensity_absolutelyContinuous (K x) (fun y => h y / h x)).ae_le
  filter_upwards [ae_lt_top hh hfinite] with y hy
  exact hy.ne

end ProbabilityTheory.Kernel

end
