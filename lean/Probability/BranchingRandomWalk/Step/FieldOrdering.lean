import Probability.BranchingRandomWalk.Step.Field
import Probability.BranchingRandomWalk.Step.Ordering
import Probability.BranchingRandomWalk.Tree.Filtration

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

/-! ## Generation-domain measurability

The next definitions apply one deterministic measurable ordering rule to the
canonical pre-sampled step field.  Unlike an arbitrary random ordering
witness, this observation reads only the step stored at the indicated node,
so its exact generation of observability can be proved.
-/

/-- The optional first displacement read from node `u` of a pre-sampled
deterministic step field. -/
def MeasurableStepOrdering.firstAtNode
    {α κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (u : TreeNode α) :
    Combinatorics.Branching.StepField α X → Option X :=
  fun field => R.first? (field u)

/-- A depth-`d` node's first displacement is observable from generation
`d + 1`, when that node's reproduction step is revealed. -/
theorem MeasurableStepOrdering.firstAtNode_measurable_next
    {α κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (u : TreeNode α) :
    @Measurable (Combinatorics.Branching.StepField α X) (Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X)
        (u.length + 1))
      Combinatorics.Branching.stepOptionMeasurableSpace (R.firstAtNode u) :=
  R.first?_measurable.comp
    (mark_measurable_next (M := Combinatorics.Branching.Step α X) u)

/-- More generally, the node observation belongs to every later generation
domain. -/
theorem MeasurableStepOrdering.firstAtNode_measurable_of_depth_lt
    {α κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (u : TreeNode α) (n : ℕ)
    (hu : u.length < n) :
    @Measurable (Combinatorics.Branching.StepField α X) (Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X) n)
      Combinatorics.Branching.stepOptionMeasurableSpace (R.firstAtNode u) :=
  R.first?_measurable.comp
    (mark_measurable_of_depth_lt
      (M := Combinatorics.Branching.Step α X) u n hu)

/-- The first displacement remains generation-measurable when the node is
itself selected using current information, provided its reproduction mark has
already been revealed. -/
theorem MeasurableStepOrdering.firstAtSelectedNode_measurable
    {α κ X : Type*} [MeasurableSpace X] [Countable α]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (n : ℕ)
    (chosen : Combinatorics.Branching.StepField α X → TreeNode α)
    (hchosen : @Measurable (Combinatorics.Branching.StepField α X)
      (TreeNode α)
      (generationFiltration (M := Combinatorics.Branching.Step α X) n)
      inferInstance chosen)
    (hdepth : ∀ field, (chosen field).length < n) :
    @Measurable (Combinatorics.Branching.StepField α X) (Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X) n)
      Combinatorics.Branching.stepOptionMeasurableSpace
      (fun field => R.first? (field (chosen field))) :=
  R.first?_measurable.comp
    (selected_mark_measurable n chosen hchosen hdepth)

/-- The generation-`n` frontier of optional first displacements, zeroed out
away from depth `n`. -/
def MeasurableStepOrdering.firstFrontier
    {α κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (n : ℕ)
    (field : Combinatorics.Branching.StepField α X) :
    TreeNode α → Option X :=
  fun u => if u.length = n then R.first? (field u) else none

/-- The first-displacement frontier at depth `n` is observable at generation
`n + 1`. -/
theorem MeasurableStepOrdering.firstFrontier_measurable
    {α κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X]
    (R : MeasurableStepOrdering α κ X) (n : ℕ) :
    @Measurable (Combinatorics.Branching.StepField α X)
      (TreeNode α → Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X) (n + 1))
      (@MeasurableSpace.pi (TreeNode α) (fun _ => Option X)
        (fun _ => Combinatorics.Branching.stepOptionMeasurableSpace))
      (R.firstFrontier n) := by
  apply (@measurable_pi_iff
    (Combinatorics.Branching.StepField α X) (TreeNode α)
    (fun _ => Option X)
    (generationFiltration (M := Combinatorics.Branching.Step α X) (n + 1))
    (fun _ => Combinatorics.Branching.stepOptionMeasurableSpace)
    (R.firstFrontier n)).2
  intro u
  by_cases hu : u.length = n
  · change @Measurable (Combinatorics.Branching.StepField α X) (Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X) (n + 1))
      Combinatorics.Branching.stepOptionMeasurableSpace
      (fun field => if u.length = n then R.first? (field u) else none)
    have h := R.firstAtNode_measurable_of_depth_lt u (n + 1)
      (by rw [hu]; exact Nat.lt_succ_self n)
    change @Measurable (Combinatorics.Branching.StepField α X) (Option X)
      (generationFiltration (M := Combinatorics.Branching.Step α X) (n + 1))
      Combinatorics.Branching.stepOptionMeasurableSpace
      (fun field => R.first? (field u)) at h
    simpa [hu] using h
  · simp [MeasurableStepOrdering.firstFrontier, hu]

end ProbabilityTheory.BranchingRandomWalk
