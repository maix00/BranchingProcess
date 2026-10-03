module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Iterated additive convolution

Mathlib defines convolution of measures but currently has no natural-number
convolution power.  This definition is public measure-theoretic infrastructure;
it does not assign an unconditional monoid structure to all measures.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {E : Type*} [AddMonoid E] [MeasurableSpace E]

/-- The `n`-fold additive convolution, with the Dirac unit at zero. -/
noncomputable def convPower (μ : Measure E) : ℕ → Measure E
  | 0 => dirac 0
  | n + 1 => μ ∗ convPower μ n

@[simp] theorem convPower_zero (μ : Measure E) :
    convPower μ 0 = dirac 0 := rfl

@[simp] theorem convPower_succ (μ : Measure E) (n : ℕ) :
    convPower μ (n + 1) = μ ∗ convPower μ n := rfl

theorem isProbabilityMeasure_convPower (μ : Measure E)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convPower μ n) := by
  induction n with
  | zero =>
      rw [convPower_zero]
      infer_instance
  | succ n ih =>
      rw [convPower_succ]
      show IsProbabilityMeasure
        (Measure.map (fun p : E × E => p.1 + p.2)
          (μ.prod (convPower μ n)))
      infer_instance

noncomputable instance convPower.instSFinite (μ : Measure E) [SFinite μ]
    (n : ℕ) : SFinite (convPower μ n) := by
  induction n with
  | zero =>
      rw [convPower_zero]
      infer_instance
  | succ n ih =>
      rw [convPower_succ]
      infer_instance

/-- The left-recursive convolution power retained for compatibility with
random-walk developments that build a sum one increment at a time. -/
noncomputable def convPow (μ : Measure E) : ℕ → Measure E
  | 0 => dirac 0
  | n + 1 => convPow μ n ∗ μ

@[simp] theorem convPow_zero (μ : Measure E) :
    convPow μ 0 = dirac 0 := rfl

@[simp] theorem convPow_succ (μ : Measure E) (n : ℕ) :
    convPow μ (n + 1) = convPow μ n ∗ μ := rfl

noncomputable instance convPow.instSFinite [MeasurableAdd₂ E]
    (μ : Measure E) [SFinite μ] (n : ℕ) : SFinite (convPow μ n) := by
  induction n with
  | zero =>
      rw [convPow_zero]
      infer_instance
  | succ n ih =>
      rw [convPow_succ]
      infer_instance

noncomputable instance convPow.instIsProbabilityMeasure [MeasurableAdd₂ E]
    [MeasurableSingletonClass E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero =>
      rw [convPow_zero]
      infer_instance
  | succ n ih =>
      rw [convPow_succ]
      infer_instance

section Comparison

variable [MeasurableAdd₂ E]

private theorem convPower_rotate (μ : Measure E) [SFinite μ] (n : ℕ) :
    convPower μ n ∗ μ = μ ∗ convPower μ n := by
  induction n with
  | zero =>
      simp [convPower_zero]
  | succ n ih =>
      calc
        convPower μ (n + 1) ∗ μ = (μ ∗ convPower μ n) ∗ μ := by
          rw [convPower_succ]
        _ = μ ∗ (convPower μ n ∗ μ) := conv_assoc _ _ _
        _ = μ ∗ (μ ∗ convPower μ n) := by rw [ih]
        _ = μ ∗ convPower μ (n + 1) := by rw [convPower_succ]

/-- The two recursive conventions for convolution powers agree when the
increment measure is S-finite. Associativity rotates the repeated factors. -/
theorem convPow_eq_convPower (μ : Measure E) [SFinite μ] (n : ℕ) :
    convPow μ n = convPower μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [convPow_succ, convPower_succ, ih]
      exact convPower_rotate μ n

end Comparison

end MeasureTheory.Measure

end
