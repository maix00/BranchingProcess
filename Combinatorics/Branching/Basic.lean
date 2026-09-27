import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Branching as the unmarked branching-walk specialization

`RootIndexed.Process Root α` is exactly a root-indexed branching walk whose
mark type is `PUnit`. Thus it retains child presence and genealogy and carries
no spatial displacement. `Process α` is its single-root case. Trees are a
further projection of these objects onto their surviving address sets.
-/

namespace Combinatorics.Branching

/-- A root-indexed branching object with no spatial marks. -/
abbrev RootIndexed.Process (Root α : Type*) :=
  RootIndexed.BranchingWalk Root α PUnit.{1} PUnit.{1}

/-- A single-root branching object with no spatial marks. -/
abbrev Process (α : Type*) := RootIndexed.Process PUnit.{1} α

/-- Regard a raw unit-marked step field as a single-root branching object. -/
def branchingOfStepField {α : Type*} (β : StepField α PUnit.{1}) :
    Process α where
  step _ := β
  initial _ := PUnit.unit
  parentClosed _ := isParentClosed_of_surviveAlong_prefix β

@[simp] theorem branchingOfStepField_step {α : Type*}
    (β : StepField α PUnit) :
    (branchingOfStepField β).step PUnit.unit = β := rfl

/-- Packaging a unit-marked step field as a branching process is measurable. -/
theorem measurable_branchingOfStepField {α : Type*} :
    Measurable (branchingOfStepField (α := α)) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap branchingOfStepField
      (MeasurableSpace.comap
        (fun β : Process α => (β.step, β.initial)) _) ≤
    (inferInstance : MeasurableSpace (StepField α PUnit.{1}))
  rw [MeasurableSpace.comap_comp]
  have hstep : Measurable
      (fun β : StepField α PUnit.{1} => fun _ : PUnit.{1} => β) := by
    rw [measurable_pi_iff]
    intro r
    exact measurable_id
  have hinitial : Measurable
      (fun _ : StepField α PUnit.{1} =>
        fun _ : PUnit.{1} => PUnit.unit.{1}) :=
    measurable_const
  have hfun :
      (fun β : Process α => (β.step, β.initial)) ∘ branchingOfStepField =
        (fun β : StepField α PUnit.{1} =>
          (fun _ : PUnit.{1} => β, fun _ : PUnit.{1} => PUnit.unit.{1})) := by
    rfl
  rw [hfun]
  exact (hstep.prodMk hinitial).comap_le

end Combinatorics.Branching
