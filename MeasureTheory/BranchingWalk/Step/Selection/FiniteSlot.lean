/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.FiniteSlot
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of the binary-slot offspring encoding

For a measurable finite selector `R`, the encoded step
`ξ ↦ R.binaryOffspringStep ξ` is measurable. Its definition is combinatorial;
this result records the measurable-space property of that construction.

## Public declarations

- `Combinatorics.Branching.Step.FiniteSelection.binaryOffspringStep_measurable`:
  if `R` is a measurable finite selection from branching steps, with countable
  measurable slots carrying a linear order and bottom element, then its
  binary-slot encoding is measurable:
  `Measurable (R.binaryOffspringStep)`.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching.Step.FiniteSelection

/-- A measurable finite selection has a measurable binary-slot offspring
encoding. -/
theorem binaryOffspringStep_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Combinatorics.Branching.Step.FiniteSelection α X)
    (hR : Measurable R.select) :
    Measurable (binaryOffspringStep R) := by
  apply measurable_pi_iff.mpr
  intro i
  have hcard : Measurable (fun ξ : Combinatorics.Branching.Step α X =>
      (R ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hR
  have hset : MeasurableSet
      {ξ : Combinatorics.Branching.Step α X | i.val < (R ξ).card} := by
    change MeasurableSet
      ((fun ξ : Combinatorics.Branching.Step α X => (R ξ).card) ⁻¹'
        Set.Ioi i.val)
    exact hcard (by simp)
  simpa [binaryOffspringStep] using
    (Measurable.ite hset
      (measurable_const : Measurable fun _ : Combinatorics.Branching.Step α X =>
        some PUnit.unit)
      (measurable_const : Measurable fun _ : Combinatorics.Branching.Step α X =>
        (none : Option PUnit)))

end Combinatorics.Branching.Step.FiniteSelection

end
