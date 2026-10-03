module

public import Combinatorics.BranchingWalk.Step.Map

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

end Combinatorics.Branching

end
