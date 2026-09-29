module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Convolution powers of measures

This file provides the additive convolution power of a measure.  It is a
measure-level construction and does not depend on random walks or stochastic
processes.
-/

open scoped MeasureTheory

@[expose] public section

namespace MeasureTheory.Measure

variable {E : Type*} [AddMonoid E] [MeasurableSpace E]

/-- The `n`-fold additive convolution of `μ`; the zeroth convolution power is
the point mass at the additive identity. -/
noncomputable def convPow (μ : Measure E) : ℕ → Measure E
  | 0 => dirac 0
  | n + 1 => convPow μ n ∗ μ

@[simp] theorem convPow_zero (μ : Measure E) :
    convPow μ 0 = dirac 0 := rfl

@[simp] theorem convPow_succ (μ : Measure E) (n : ℕ) :
    convPow μ (n + 1) = convPow μ n ∗ μ := rfl

noncomputable instance convPow.instSFinite [MeasurableAdd₂ E]
    [MeasurableSingletonClass E] (μ : Measure E) [SFinite μ] (n : ℕ) :
    SFinite (convPow μ n) := by
  induction n with
  | zero =>
      rw [convPow]
      infer_instance
  | succ n ih =>
      rw [convPow]
      infer_instance

noncomputable instance convPow.instIsProbabilityMeasure [MeasurableAdd₂ E]
    [MeasurableSingletonClass E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero =>
      rw [convPow]
      infer_instance
  | succ n ih =>
      rw [convPow]
      infer_instance

end MeasureTheory.Measure
