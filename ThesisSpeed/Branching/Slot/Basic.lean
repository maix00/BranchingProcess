import ThesisSpeed.Probability.Branching.PointProcess.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The real child-slot vocabulary

The thesis's branching step is the abstract `BranchingStep ℕ ℝ`: slot `i`
holds `some x` when the `i`th optional child is present at displacement `x`,
and `none` otherwise. A slot is present exactly when it holds a child, so the
empty point process is the all-absent step; this encodes finite and countably
infinite child sets without imposing survival. This module collects the slot
vocabulary used by the paper's arguments (`Ξ₁`, `Ξ₂`, ...).
-/

open MeasureTheory

namespace ThesisSpeed

/-- Displacement of child slot `i`, whether or not that slot is present. -/
def childDisplacement (ξ : NatRealBranchingStep) (i : ℕ) : ℝ :=
  branchingStepIncrement ξ i

def firstDisplacement (ξ : NatRealBranchingStep) : ℝ := childDisplacement ξ 0

def childPresent (i : ℕ) : Set NatRealBranchingStep :=
  {ξ | branchingStepPresent ξ i}

theorem childPresent_measurable (i : ℕ) :
    MeasurableSet (childPresent i) :=
  branchingStepPresent_measurableSet i

theorem childDisplacement_measurable (i : ℕ) :
    Measurable (fun ξ : NatRealBranchingStep => childDisplacement ξ i) :=
  branchingStepIncrement_measurable i

/-- The child point process has at least one realized atom. This is a
property of a mark, not part of the ambient mark type. -/
def childNonempty : Set NatRealBranchingStep :=
  {ξ | ∃ i : ℕ, ξ ∈ childPresent i}

theorem childNonempty_measurable : MeasurableSet childNonempty := by
  have hset : childNonempty = ⋃ i : ℕ, childPresent i := by
    ext ξ
    simp [childNonempty]
  rw [hset]
  exact MeasurableSet.iUnion childPresent_measurable

/-- The child point process has at least two distinct realized children. -/
def twoChildren : Set NatRealBranchingStep :=
  {ξ | ∃ i j : ℕ, i ≠ j ∧ ξ ∈ childPresent i ∧ ξ ∈ childPresent j}

theorem twoChildren_measurable : MeasurableSet twoChildren := by
  have hset : twoChildren =
      ⋃ i : ℕ, ⋃ j : ℕ, if i = j then ∅ else childPresent i ∩ childPresent j := by
    ext ξ
    simp [twoChildren]
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact MeasurableSet.empty
  · exact (childPresent_measurable i).inter (childPresent_measurable j)

/-- The causal one-or-two-child rule keeps the first child and accepts the
second only if it exists and its displacement is at most `M`. -/
def keepSecond (M : ℝ) : Set NatRealBranchingStep :=
  {ξ | ξ ∈ childPresent 1 ∧ childDisplacement ξ 1 ≤ M}

theorem keepSecond_measurable (M : ℝ) : MeasurableSet (keepSecond M) := by
  change MeasurableSet
    (childPresent 1 ∩
      {ξ : NatRealBranchingStep | childDisplacement ξ 1 ∈ Set.Iic M})
  exact (childPresent_measurable 1).inter
    ((childDisplacement_measurable 1) measurableSet_Iic)

/-- The fully truncated law keeps the first child only when it exists and
its displacement is at most `M`. Unlike the backbone law, this can discard
every child. -/
def keepFirst (M : ℝ) : Set NatRealBranchingStep :=
  {ξ | ξ ∈ childPresent 0 ∧ childDisplacement ξ 0 ≤ M}

theorem keepFirst_measurable (M : ℝ) : MeasurableSet (keepFirst M) := by
  change MeasurableSet
    (childPresent 0 ∩
      {ξ : NatRealBranchingStep | childDisplacement ξ 0 ∈ Set.Iic M})
  exact (childPresent_measurable 0).inter
    ((childDisplacement_measurable 0) measurableSet_Iic)

noncomputable def retainedChildrenCount (M : ℝ) (ξ : NatRealBranchingStep) : ℕ := by
  classical
  exact (if ξ ∈ childPresent 0 then 1 else 0) +
    (if ξ ∈ keepSecond M then 1 else 0)

theorem retainedChildrenCount_measurable (M : ℝ) :
    Measurable (retainedChildrenCount M) := by
  classical
  unfold retainedChildrenCount
  exact ((measurable_const).ite (childPresent_measurable 0)
    measurable_const).add
      ((measurable_const).ite (keepSecond_measurable M) measurable_const)

theorem retainedChildrenCount_le_two (M : ℝ) (ξ : NatRealBranchingStep) :
    retainedChildrenCount M ξ ≤ 2 := by
  classical
  unfold retainedChildrenCount
  split_ifs <;> omega

/-- Number of children in the fully truncated law `Ξ⁽ᴹ⁾`; it can be zero. -/
noncomputable def truncatedChildrenCount (M : ℝ)
    (ξ : NatRealBranchingStep) : ℕ := by
  classical
  exact (if ξ ∈ keepFirst M then 1 else 0) +
    (if ξ ∈ keepSecond M then 1 else 0)

theorem truncatedChildrenCount_measurable (M : ℝ) :
    Measurable (truncatedChildrenCount M) := by
  classical
  unfold truncatedChildrenCount
  exact ((measurable_const).ite (keepFirst_measurable M)
    measurable_const).add
      ((measurable_const).ite (keepSecond_measurable M) measurable_const)

theorem truncatedChildrenCount_le_two (M : ℝ) (ξ : NatRealBranchingStep) :
    truncatedChildrenCount M ξ ≤ 2 := by
  classical
  unfold truncatedChildrenCount
  split_ifs <;> omega

end ThesisSpeed
