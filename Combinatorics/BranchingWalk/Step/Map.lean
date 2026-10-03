module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Mapping branching-step marks

A branching step has two independent pieces of information: which slots are
present and the mark carried by each present slot. `Step.map` changes only the
marks. The survival set is therefore invariant. Maps of complete step fields
and branching walks live in `Combinatorics/BranchingWalk/Basic/Map.lean`.
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

/-- Forget every child mark while retaining exactly the child slots. -/
def Step.forgetMark {ι X : Type*} (ξ : Step ι X) : Step ι PUnit.{1} :=
  ξ.map (fun _ => PUnit.unit.{1})

@[simp] theorem survive_forgetMark_iff {ι X : Type*} (ξ : Step ι X) (i : ι) :
    survive ξ.forgetMark i ↔ survive ξ i :=
  survive_map_iff _ _ _

end Combinatorics.Branching

end
