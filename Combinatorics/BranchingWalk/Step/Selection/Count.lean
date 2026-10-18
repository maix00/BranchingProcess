/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Map
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Child counts of a branching step

The number of children is the extended cardinality of the set of present
slots. The value `∞` is retained, so no finiteness assumption is built into
the observation.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- The possibly infinite number of children in a branching step. -/
noncomputable def Step.childCount {ι X : Type*} (ξ : Step ι X) : ℕ∞ :=
  (support ξ).encard

@[simp] theorem Step.childCount_map {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) :
    (ξ.map f).childCount = ξ.childCount := by
  simp [Step.childCount]

@[simp] theorem Step.childCount_forgetMark {ι X : Type*} (ξ : Step ι X) :
    ξ.forgetMark.childCount = ξ.childCount := by
  simp [Step.childCount, Step.forgetMark]

/-- The extended child count is measurable when the slot type is countable. -/
theorem Step.childCount_measurable {ι X : Type*} [Countable ι]
    [MeasurableSpace X] :
    Measurable (Step.childCount : Step ι X → ℕ∞) := by
  unfold Step.childCount
  apply measurable_encard.comp
  rw [measurable_set_iff]
  intro i
  exact measurable_to_prop (by simpa [support] using survive_measurableSet i)

end Combinatorics.Branching

end
