/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# S-finite kernel powers

## Public declarations

* `ProbabilityTheory.IsSFiniteKernel.pow`: for an s-finite kernel `K`,
  the native iterate `K ^ n` is s-finite for every natural `n`.

The proof uses closure under composition and the deterministic identity kernel.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped ProbabilityTheory

instance IsSFiniteKernel.pow {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (K ^ n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [pow_succ]
    change IsSFiniteKernel ((K ^ n) ∘ₖ K)
    infer_instance

end ProbabilityTheory

end
