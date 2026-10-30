/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Kernel transitions between measurable subsets

## Public declarations

- `bridgeKernel` restricts the initial state to a measurable source set and
  the endpoint to a measurable target set for a fixed power of a kernel.
- `bridgeKernel_apply` identifies its value on a measurable target subset
  with the ambient transition mass of its subtype image;
  `bridgeKernel_apply_univ` specializes this identity to the full target.

The construction applies to every kernel and finite time horizon. It packages
Mathlib's kernel powers and measurable subtype embeddings as a transition
between two measurable state spaces.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Run an ambient kernel for a fixed number of steps, starting in a source
subtype and retaining only endpoints in a measurable target subtype. -/
noncomputable def bridgeKernel (K : Kernel S S)
    (source target : Set S) (htarget : MeasurableSet target)
    (length : ℕ) : Kernel source target :=
  ((K ^ length).comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe htarget)

/-- Evaluation of a bridge kernel on a target set is the ambient block
transition mass of its subtype image. -/
theorem bridgeKernel_apply
    (K : Kernel S S) (source target : Set S) (htarget : MeasurableSet target)
    (length : ℕ) (x : source) (A : Set target) (hA : MeasurableSet A) :
    bridgeKernel K source target htarget length x A =
      (K ^ length) (x : S) (Subtype.val '' A) := by
  rw [bridgeKernel, Kernel.comapRight_apply' _
    (MeasurableEmbedding.subtype_coe htarget) x hA, Kernel.comap_apply']

/-- The mass of a bridge kernel is the ambient transition mass of its target
set. -/
theorem bridgeKernel_apply_univ
    (K : Kernel S S) (source target : Set S) (htarget : MeasurableSet target)
    (length : ℕ) (x : source) :
    bridgeKernel K source target htarget length x Set.univ =
      (K ^ length) (x : S) target := by
  rw [bridgeKernel_apply K source target htarget length x Set.univ
    MeasurableSet.univ]
  simp

end ProbabilityTheory.Kernel

end
