import MeasureTheory.BranchingWalk.Position.Displace
import MeasureTheory.BranchingWalk.Prefix
import MeasureTheory.BranchingWalk.Tree.Realization
import MeasureTheory.UlamHarris.MarkedTree.Basic

/-!
# The realized tree of an ordered step field

`realizedTree step hordered` is the deterministic tree whose carrier
is exactly the realized addresses; the ordered-sibling axiom follows from the
presence-prefix half of `OrderedStep`. `markedTree` then
marks every realized node by its displacement, which is the bridge from
the step field to the `MarkedTree` object of the paper.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- The deterministic tree realized by an ordered step field. -/
def realizedTree {α X : Type*} [LT α] [LE X]
    (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u)) : UlamHarris.Tree α where
  carrier := {u | realizedNode step u}
  root_mem := realizedNode_nil step
  prefix_closed := by
    intro u v huv
    change realizedNode step (u ++ v) at huv
    exact (realizedNode_append_iff step u v).1 huv |>.1
  sibling_closed := by
    intro u i j hj hij
    change realizedNode step (u ++ [j]) at hj
    rw [realizedNode_append_singleton_iff] at hj
    exact (realizedNode_append_singleton_iff step u i).2
      ⟨hj.1, present_of_later (step u) (hordered u).1 hij hj.2⟩

@[simp] theorem realizedTree_carrier {α X : Type*} [LT α] [LE X]
    (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u)) :
    (realizedTree step hordered).carrier =
      {u | realizedNode step u} := rfl

@[simp] theorem mem_realizedTree_iff {α X : Type*} [LT α] [LE X]
    (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u)) (u : TreeNode α) :
    u ∈ (realizedTree step hordered).carrier ↔
      realizedNode step u := Iff.rfl

/-- The marked tree of an ordered step field: the realized addresses carry
their displacements. This is the bridge from the step field to the
tree-with-marks object; both the realized tree and the marks are derived from
the field. -/
def markedTree {α X : Type*} [AddCommMonoid X] [LT α] [LE X]
    (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u)) : MarkedTree α X where
  tree := realizedTree step hordered
  mark := fun u _ => displaceRoot step u

@[simp] theorem markedTree_tree {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u)) :
    (markedTree step hordered).tree =
      realizedTree step hordered := rfl

@[simp] theorem markedTree_mark {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : StepField α X)
    (hordered : ∀ u, OrderedStep (step u))
    (u : TreeNode α) (hu : u ∈ (realizedTree step hordered).carrier) :
    (markedTree step hordered).mark u hu =
      displaceRoot step u := rfl

end BranchingWalk

end MeasureTheory
