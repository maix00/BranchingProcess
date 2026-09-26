import Combinatorics.BranchingWalk.Tree.Correspondence.Basic

/-!
# Ordered step fields are labelled branching marked trees

A branching random walk can be surviveed in two ways: as a step field, giving
the relative displacement of every child of every address, or as a marked tree,
giving the position of every realized node. This file records that the two
surviveations carry the same information.

The reading `stepOfMarkedTree` of `Correspondence/Basic.lean` is inverse to
`markedTree` on the part of a field that the tree sees. Below the realized tree
a field may still carry arbitrary data, and a tree records none of it, so the
exact statement normalizes the field:

* `RealizedSupport step` says that every slot of an unrealized address is
  absent, so the realized tree determines the field.
* `IsBranchingMarkedTree M` says that the root mark of `M` vanishes and that its
  sibling marks increase, which is the thesis's convention of listing the
  children of a node by increasing displacement.

`realizedParentClosedBranchingWalkEquivMarkedTree` is then the bijection between these
two subtypes. It is stated over an additive group, because reading the relative
displacement of a node off its mark uses subtraction.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {α X : Type*} [LT α]

/-- A step field carries no data below its realized tree: every slot of an
address that is not realized is absent. The realized tree of such a field
determines the field, so this is the normalization under which reading a field
off a marked tree is inverse to marking a step field. -/
def RealizedSupport (step : StepField α X) : Prop :=
  ∀ u, ¬ surviveAlong step [] step u → ∀ i, step u i = none

section

variable [LE X]

/-- The ordered step fields of the correspondence: ordered, and carrying no
data below their realized tree. -/
abbrev RealizedParentClosedBranchingWalk (α X : Type*) [LT α] [LE X] :=
  {step : ParentClosedBranchingWalk α X //
    (∀ u, IsMonotone (step.1 u)) ∧ RealizedSupport step.1}

/-- The marked trees of the correspondence: the root mark vanishes and the
sibling marks increase. -/
abbrev IsBranchingMarkedTree [Zero X] (M : MarkedTree α X) : Prop :=
  M.rootMark = 0 ∧ M.siblingMonotone

end

section

variable [AddCommMonoid X]

/-- The root mark of the marked tree of a step field vanishes. -/
theorem rootMark_markedTree (step : StepField α X)
    (hpresence : ∀ u, Step.IsSiblingClosed (step u)) :
    (markedTree step hpresence).rootMark = 0 := rfl

end

section

variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]

/-- Ordered step fields with no data below their realized tree are exactly the
marked trees with vanishing root mark and increasing sibling marks. The forward
map marks every realized node by its displacement, the inverse reads the
relative displacement of every realized child off the tree. -/
noncomputable def realizedParentClosedBranchingWalkEquivMarkedTree :
    RealizedParentClosedBranchingWalk α X ≃
      {M : MarkedTree α X // IsBranchingMarkedTree M} where
  toFun step :=
    ⟨markedTree step.1.1 step.1.2.2,
      rootMark_markedTree step.1.1 _,
      siblingMonotone_markedTree step.1.1 step.1.2.2 step.2.1⟩
  invFun M :=
    ⟨⟨stepOfMarkedTree M.1,
        ⟨fun u v h => (surviveAlong_root_stepOfMarkedTree_iff (u ++ v)).1 h,
          fun u => Step.IsSiblingClosed_stepOfMarkedTree u⟩⟩,
      ⟨fun u => (monotone_stepOfMarkedTree_iff u).2 (by
            intro i j hi hj hij
            exact M.2.2 u i j hi hj hij),
      fun u hu i => by
        refine stepOfMarkedTree_apply_of_notMem (M := M.1) fun hmem => hu ?_
        exact ((surviveAlong_root_append_singleton_iff (stepOfMarkedTree M.1) u i).1
          ((surviveAlong_root_stepOfMarkedTree_iff (u ++ [i])).2 hmem)).1⟩⟩
  left_inv step := by
    refine Subtype.ext (Subtype.ext (funext fun u => funext fun i => ?_))
    show stepOfMarkedTree (markedTree step.1.1 step.1.2.2) u i =
      step.1.1 u i
    by_cases hu : surviveAlong step [] step.1.1 u
    · rw [stepOfMarkedTree_markedTree_of_realized step.1.1 _ hu]
    · have hmem : u ++ [i] ∉
          (markedTree step.1.1 step.1.2.2).tree.carrier :=
        fun h => hu ((surviveAlong_root_append_singleton_iff step.1.1 u i).1 h).1
        rw [stepOfMarkedTree_apply_of_notMem (M := markedTree step.1.1 _) hmem,
        step.1.2.2 u hu i]
  right_inv M := Subtype.ext (markedTree_stepOfMarkedTree M.1 M.2.1)

end

end Branching

end Combinatorics
