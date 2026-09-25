import Combinatorics.BranchingStep.Prefix

/-!
# Increments and support of a branching step

`branchingStepIncrement` is the mark of a present slot and the zero of the
value monoid for an absent one, so it is defined on every slot. The support is
the set of present slots, and an increasing order condition makes the
increment monotone in the slot label.
-/

namespace BranchingStep

def branchingStepIncrement {X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) : X :=
  (ξ i).getD 0

theorem branchingStepIncrement_measurable
    {ι X : Type*} [MeasurableSpace X] [Zero X] (i : ι) :
    Measurable (fun ξ : BranchingStep ι X => branchingStepIncrement ξ i) := by
  unfold branchingStepIncrement
  exact (measurable_optionGetD (0 : X)).comp (measurable_pi_apply i)

theorem branchingStepIncrement_none {ι X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) (h : ξ i = none) :
    branchingStepIncrement ξ i = 0 := by
  simp [branchingStepIncrement, h]

theorem branchingStepIncrement_some {ι X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) (x : X) (h : ξ i = some x) :
    branchingStepIncrement ξ i = x := by
  simp [branchingStepIncrement, h]

def branchingStepSupport {ι X : Type*} (ξ : BranchingStep ι X) : Set ι :=
  {i | branchingStepPresent ξ i}

theorem branchingStep_support_finite_of_fintype
    {ι X : Type*} [Fintype ι] (ξ : BranchingStep ι X) :
    (branchingStepSupport ξ).Finite := Set.toFinite _
theorem branchingStepIncrement_mono_of_present
    {X : Type*} [Zero X] [Preorder X]
    (ξ : BranchingStep ℕ X) (hordered : branchingStepPrefixOrdered ξ)
    {i j : ℕ} (hij : i ≤ j)
    (hi : branchingStepPresent ξ i) (hj : branchingStepPresent ξ j) :
    branchingStepIncrement ξ i ≤ branchingStepIncrement ξ j := by
  rcases hi with ⟨x, hx⟩
  rcases hj with ⟨y, hy⟩
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij heq
    rw [branchingStepIncrement_some ξ i x hx,
      branchingStepIncrement_some ξ j y hy]
    exact hordered i j x y hlt hx hy

end BranchingStep
