module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Mapping branching-step marks

A branching step records which slots are present and the marks carried by
those children. `Step.map` changes only the marks, so the survival set is
invariant. Maps of complete step fields live in
`Combinatorics/BranchingWalk/StepField.lean`; maps of branching walks live in
`Combinatorics/BranchingWalk/Basic/Map.lean`.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- Map the mark of every present child, preserving absent slots. -/
def Step.map {ι X Y : Type*} (f : X → Y) (ξ : Step ι X) : Step ι Y :=
  fun i => (ξ i).map f

@[simp] theorem Step.map_apply {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) (i : ι) :
    ξ.map f i = (ξ i).map f := rfl

@[simp] theorem Step.map_id {ι X : Type*} (ξ : Step ι X) :
    ξ.map id = ξ := by
  funext i
  simp [Step.map]

@[simp] theorem Step.map_map {ι X Y Z : Type*} (g : Y → Z) (f : X → Y)
    (ξ : Step ι X) :
    (ξ.map f).map g = ξ.map (g ∘ f) := by
  funext i
  simp [Step.map]

@[simp] theorem survive_map_iff {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) (i : ι) :
    survive (ξ.map f) i ↔ survive ξ i := by
  cases h : ξ i <;> simp [Step.map, survive, h]

@[simp] theorem Step.support_map {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) :
    support (ξ.map f) = support ξ := by
  ext i
  simp [support]

/-- Mapping the marks coordinatewise is measurable when the mark map is
measurable. -/
theorem Step.map_measurable {ι X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : Measurable f) :
    Measurable (Step.map (ι := ι) f) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_option_map hf).comp (measurable_pi_apply i)

/-- Forget every child mark while retaining exactly the child slots. -/
def Step.forgetMark {ι X : Type*} (ξ : Step ι X) : Step ι PUnit.{1} :=
  ξ.map (fun _ => PUnit.unit.{1})

@[simp] theorem survive_forgetMark_iff {ι X : Type*} (ξ : Step ι X) (i : ι) :
    survive ξ.forgetMark i ↔ survive ξ i :=
  survive_map_iff _ _ _

end Combinatorics.Branching

end
