/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import MeasureTheory.Measure.WithDensity

/-!
# Exponentially tilted laws of random measures

This construction starts from a law on measures over an arbitrary measurable
space.  It uses integration against each sampled measure and therefore does
not require an enumeration of its atoms or a countable ambient space.

## Public declarations

- `exponentialWeight` and `weightedImage` define
  $w(x)=e^{\theta F(x)}$ and $(w\nu)\circ F^{-1}$; `tiltedLaw` is the
  mixture of these weighted image measures under a law on measures.
- `exponentialWeight_measurable` and `weightedImage_measurable` provide the
  measurability needed for this construction; the general fixed-density
  transformation is in `MeasureTheory.Measure.WithDensity`.
- `lintegral_weightedImage` and `lintegral_tiltedLaw` give, respectively,
  $\int f\,d((w\nu)\circ F^{-1})=\int w(x)f(F(x))\,d\nu(x)$ and the
  corresponding iterated-integral formula under the law on measures.
- `lintegral_tiltedLaw_cancel` states that multiplying by
  $e^{-\theta y}$ cancels the exponential tilt inside the integral.
- `HasNormalization` says the expected total exponential weight is $1$;
  `tiltedLaw_isProbability` proves that this condition makes the tilted law a
  probability measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomMeasure

/-- Exponential weight associated with a real-valued measurable observation. -/
noncomputable def exponentialWeight {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (x : E) : ENNReal :=
  ENNReal.ofReal (Real.exp (θ * potential x))

theorem exponentialWeight_measurable
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ) :
    Measurable (exponentialWeight potential θ) :=
  ((measurable_const.mul hpotential).exp).ennreal_ofReal

/-- Weight a measure exponentially and map it through the potential. -/
noncomputable def weightedImage
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (ν : Measure E) : Measure ℝ :=
  (ν.withDensity (exponentialWeight potential θ)).map potential

theorem weightedImage_measurable
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ) :
    Measurable (weightedImage potential θ) := by
  exact (Measure.measurable_map potential hpotential).comp
    (Measure.measurable_withDensity_fixed
      (exponentialWeight_measurable hpotential θ))

/-- The tilted real law obtained by first sampling a measure and then sampling
from its exponentially weighted potential image. -/
noncomputable def tiltedLaw
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E)) : Measure ℝ :=
  law.bind (weightedImage potential θ)

theorem lintegral_weightedImage
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ)
    (ν : Measure E) {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ y, f y ∂weightedImage potential θ ν) =
      ∫⁻ x, exponentialWeight potential θ x * f (potential x) ∂ν := by
  rw [weightedImage, lintegral_map hf hpotential]
  simpa only [Pi.mul_apply, Function.comp_apply] using
    (lintegral_withDensity_eq_lintegral_mul ν
      (exponentialWeight_measurable hpotential θ) (hf.comp hpotential))

theorem lintegral_tiltedLaw
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ)
    (law : Measure (Measure E)) {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ y, f y ∂tiltedLaw potential θ law) =
      ∫⁻ ν, ∫⁻ x,
        exponentialWeight potential θ x * f (potential x) ∂ν ∂law := by
  rw [tiltedLaw, Measure.lintegral_bind
    (weightedImage_measurable hpotential θ).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro ν
  exact lintegral_weightedImage hpotential θ ν hf

/-- Multiplication by the reciprocal exponential weight cancels the tilt and
leaves ordinary integration against the sampled measure. -/
theorem lintegral_tiltedLaw_cancel
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ)
    (law : Measure (Measure E)) {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-θ * y)) * f y
        ∂tiltedLaw potential θ law) =
      ∫⁻ ν, ∫⁻ x, f (potential x) ∂ν ∂law := by
  have htest : Measurable
      (fun y : ℝ => ENNReal.ofReal (Real.exp (-θ * y)) * f y) := by
    fun_prop
  rw [lintegral_tiltedLaw hpotential θ law htest]
  apply lintegral_congr
  intro ν
  apply lintegral_congr
  intro x
  unfold exponentialWeight
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
    ← Real.exp_add]
  have hzero : θ * potential x + -θ * potential x = 0 := by ring
  rw [hzero]
  simp

/-- Expected total exponential mass equals one. -/
def HasNormalization
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E)) : Prop :=
  (∫⁻ ν, ∫⁻ x, exponentialWeight potential θ x ∂ν ∂law) = 1

theorem tiltedLaw_isProbability
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential) (θ : ℝ)
    (law : Measure (Measure E))
    (hnormalization : HasNormalization potential θ law) :
    IsProbabilityMeasure (tiltedLaw potential θ law) := by
  rw [isProbabilityMeasure_iff]
  rw [← lintegral_one]
  rw [lintegral_tiltedLaw hpotential θ law measurable_const]
  simpa [HasNormalization] using hnormalization

end ProbabilityTheory.RandomMeasure
