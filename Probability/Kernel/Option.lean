/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.SubMarkov
public import MeasureTheory.MeasurableSpace.Option

/-!
# Kernels with an optional input

## Public declarations

* `ProbabilityTheory.Kernel.optionElim ν κ` extends a kernel on $A$ to
  $\mathrm{Option}(A)$, assigning law $\nu$ to `none` and $\kappa(a)$ to `some a`.
* `ProbabilityTheory.Kernel.optionElim_none` and `optionElim_some` give those laws.
* `ProbabilityTheory.Kernel.optionElim.isMarkovKernel` preserves probability
  kernels when $\nu$ is a probability measure.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

/-- Extend a kernel by specifying the law at the absent input. -/
noncomputable def optionElim {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) (κ : Kernel A B) : Kernel (Option A) B where
  toFun o := o.elim ν κ
  measurable' := measurable_option_elim ν κ.measurable

@[simp] theorem optionElim_none {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) (κ : Kernel A B) : optionElim ν κ none = ν := rfl

@[simp] theorem optionElim_some {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) (κ : Kernel A B) (a : A) : optionElim ν κ (some a) = κ a := rfl

instance optionElim.isMarkovKernel {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (κ : Kernel A B) [IsMarkovKernel κ] :
    IsMarkovKernel (optionElim ν κ) where
  isProbabilityMeasure o := by
    cases o <;> simp only [optionElim_none, optionElim_some] <;> infer_instance

end ProbabilityTheory.Kernel
