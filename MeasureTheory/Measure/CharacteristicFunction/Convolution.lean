/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import MeasureTheory.Measure.Convolution.Power

/-!
# Characteristic functions of convolution powers

The characteristic function turns additive convolution into multiplication,
so the characteristic function of an `n`-fold convolution is the `n`th power.
-/

@[expose] public section

namespace MeasureTheory.Measure

/-- The characteristic function of an `n`-fold convolution power is the
`n`th power of the original characteristic function. -/
theorem charFun_convPower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableAdd₂ E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (t : E) :
    charFun (μ.convPower n) t = (charFun μ t) ^ n := by
  induction n with
  | zero =>
    simp only [convPower_zero, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, pow_zero]
  | succ n ih =>
    rw [convPower_succ, charFun_conv, ih, pow_succ, mul_comm]

end MeasureTheory.Measure
