/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.DoobTransform.Basic
public import Probability.Kernel.Composition.Pow

/-!
# Composition and iteration of Doob transforms

## Public declarations

* `ProbabilityTheory.Kernel.doobTransform_comp`: for a finite positive
  measurable weight, `Lʰ ∘ Kʰ = (L ∘ K)ʰ`.
* `ProbabilityTheory.Kernel.doobTransform_pow`: native kernel powers
  satisfy `(Kʰ)^n = (K^n)ʰ`.
* `ProbabilityTheory.Kernel.lintegral_pow_doobTransform`: for measurable
  nonnegative `f`, `(Kʰ)^n f(x) = K^n(h f)(x)/h(x)`.

The proof cancels the intermediate weight in the iterated integral.
This is the iterated form of Zhan Shi, *Branching Random Walks*, LNM 2151
(2015), Chapter 4, §4.2, (4.4), DOI 10.1007/978-3-319-25372-5.
Composition and powers are Mathlib's native kernel operations.
-/

@[expose] public section

namespace ProbabilityTheory.Kernel

open MeasureTheory
open scoped ENNReal ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

/-- Finite positive weights cancel at an intermediate transition. -/
theorem doobTransform_comp (K L : Kernel S S) [IsSFiniteKernel K] [IsSFiniteKernel L]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞) :
    doobTransform L h ∘ₖ doobTransform K h = doobTransform (L ∘ₖ K) h := by
  apply Kernel.ext_fun
  intro x f hf
  rw [lintegral_comp _ _ _ hf,
    lintegral_doobTransform K hh hf.lintegral_kernel]
  simp_rw [lintegral_doobTransform L hh hf]
  have hcancel : ∀ y,
      h y * ((∫⁻ z, h z * f z ∂L y) / h y) =
        ∫⁻ z, h z * f z ∂L y := by
    intro y
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel (hzero y) (htop y), mul_one]
  simp_rw [hcancel]
  rw [lintegral_doobTransform (L ∘ₖ K) hh hf]
  congr 1
  exact (lintegral_comp L K x (hh.mul hf)).symm

/-- Doob transformation commutes with native finite kernel powers. -/
theorem doobTransform_pow (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞) (n : ℕ) :
    doobTransform K h ^ n = doobTransform (K ^ n) h := by
  induction n with
  | zero =>
    apply Kernel.ext_fun
    intro x f hf
    change (∫⁻ y, f y ∂Kernel.id x) = _
    rw [lintegral_doobTransform _ hh hf]
    change (∫⁻ y, f y ∂Kernel.id x) = (∫⁻ y, h y * f y ∂Kernel.id x) / h x
    rw [Kernel.id_apply, lintegral_dirac' _ hf]
    change f x = (∫⁻ y, (h * f) y ∂Measure.dirac x) / h x
    rw [lintegral_dirac' _ (hh.mul hf)]
    change f x = h x * f x / h x
    rw [div_eq_mul_inv, mul_comm (h x), mul_assoc,
      ENNReal.mul_inv_cancel (hzero x) (htop x), mul_one]
  | succ n ih =>
    rw [pow_succ, ih]
    change doobTransform (K ^ n) h ∘ₖ doobTransform K h =
      doobTransform ((K ^ n) ∘ₖ K) h
    exact doobTransform_comp K (K ^ n) hh hzero htop

/-- The n-step transition has the endpoint-to-start weight ratio. -/
theorem lintegral_pow_doobTransform (K : Kernel S S) [IsSFiniteKernel K]
    {h f : S → ℝ≥0∞} (hh : Measurable h) (hf : Measurable f)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞) (n : ℕ) (x : S) :
    (∫⁻ y, f y ∂(doobTransform K h ^ n) x) =
      (∫⁻ y, h y * f y ∂(K ^ n) x) / h x := by
  rw [doobTransform_pow K hh hzero htop n, lintegral_doobTransform _ hh hf]

end ProbabilityTheory.Kernel

end
