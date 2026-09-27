import Probability.BranchingRandomWalk.Step.Field
import Probability.BranchingRandomWalk.Step.Ordering

/-!
# Measurable ordered observations at every tree node

A step field contains a fresh random branching step at every Ulam--Harris
address.  Orderability is therefore a nodewise property.  This file defines
the optional first displacement `(Ξ_u)₁` at each fixed node and proves both
its coordinate measurability and joint measurability as an `Option X`-valued
field.  The optional codomain records the legitimate zero-child case.

This does not relabel descendant addresses.  Transporting whole descendant
subtrees under the nodewise slot permutations is a separate tree-level
construction.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris

/-- Every random step at a tree node admits a measurable ordered realization
with common ordered slot type `κ`. -/
def StepField.IsMeasurablyOrderable
    {Ω α X : Type*} (κ : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : StepField Ω α X) : Prop :=
  ∀ u, (S u).IsMeasurablyOrderable κ

/-- The optional first displacement `(Ξ_u)₁` at a fixed reproduction node.
It is `none` exactly when the ordered realization has no child. -/
noncomputable def StepField.firstDisplacement?
    {Ω α κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (S : StepField Ω α X) (h : S.IsMeasurablyOrderable κ)
    (u : TreeNode α) : Ω → Option X :=
  (S u).leftmostDisplacement? (h u)

theorem StepField.firstDisplacement?_measurable
    {Ω α κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (S : StepField Ω α X) (h : S.IsMeasurablyOrderable κ)
    (u : TreeNode α) :
    Measurable (S.firstDisplacement? h u) :=
  (S u).leftmostDisplacement?_measurable (h u)

/-- The complete field of optional first displacements, indexed by the raw
tree nodes. -/
noncomputable def StepField.firstDisplacementField?
    {Ω α κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (S : StepField Ω α X) (h : S.IsMeasurablyOrderable κ) :
    Ω → TreeNode α → Option X :=
  fun ω u => S.firstDisplacement? h u ω

/-- All nodewise first displacements are jointly measurable in the product
measurable space. -/
theorem StepField.firstDisplacementField?_measurable
    {Ω α κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (S : StepField Ω α X) (h : S.IsMeasurablyOrderable κ) :
    Measurable (S.firstDisplacementField? h) := by
  rw [measurable_pi_iff]
  intro u
  exact S.firstDisplacement?_measurable h u

/-- At any node with a child, `(Ξ_u)₁` is present and no larger than every
raw child displacement at that node. -/
theorem StepField.firstDisplacement?_eq_some_le
    {Ω α κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LinearOrder X]
    (S : StepField Ω α X) (h : S.IsMeasurablyOrderable κ)
    (ω : Ω) (u : TreeNode α)
    (hne : ∃ i, Combinatorics.Branching.survive (S u ω) i) :
    ∃ x, S.firstDisplacement? h u ω = some x ∧
      ∀ i y, S u ω i = some y → x ≤ y :=
  (S u).leftmostDisplacement?_eq_some_le (h u) ω hne

end ProbabilityTheory.BranchingRandomWalk
