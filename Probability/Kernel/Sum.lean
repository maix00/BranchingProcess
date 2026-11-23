/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Basic

/-!
# Kernels on a disjoint union of input spaces

## Public declarations

In `ProbabilityTheory.Kernel`:

* `sumElim K L` satisfies `(K ⊕ L)(inl a) = K(a)` and
  `(K ⊕ L)(inr b) = L(b)` on arbitrary measurable input spaces.
* `sumElim_inl` and `sumElim_inr` give those evaluation identities.
* `sumElim.isMarkovKernel` preserves probability kernels.

The construction uses native `Sum` and measurable elimination. It adds no
mixture distribution: the tag specifies which input kernel applies.
-/

@[expose] public section

namespace ProbabilityTheory.Kernel

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- Select an input kernel by the disjoint-union tag. -/
noncomputable def sumElim (K : Kernel A C) (L : Kernel B C) : Kernel (A ⊕ B) C where
  toFun := Sum.elim K L
  measurable' := K.measurable.sumElim L.measurable

@[simp] theorem sumElim_inl (K : Kernel A C) (L : Kernel B C) (a : A) :
    sumElim K L (Sum.inl a) = K a := rfl

@[simp] theorem sumElim_inr (K : Kernel A C) (L : Kernel B C) (b : B) :
    sumElim K L (Sum.inr b) = L b := rfl

instance sumElim.isMarkovKernel (K : Kernel A C) (L : Kernel B C)
    [IsMarkovKernel K] [IsMarkovKernel L] : IsMarkovKernel (sumElim K L) where
  isProbabilityMeasure x := by
    cases x <;> simp only [sumElim_inl, sumElim_inr] <;> infer_instance

end ProbabilityTheory.Kernel

end
