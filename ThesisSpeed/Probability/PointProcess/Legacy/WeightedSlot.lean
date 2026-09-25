import ThesisSpeed.Probability.PointProcess.RandomMeasure.BranchingStep
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The real offspring-slot vocabulary

This module is retained only while the old branching and stopping arguments are
migrated to the abstract `BranchingStep`.  A slot is present exactly when it
holds a child, so the empty point process is the all-absent step; this encodes
finite and countably infinite offspring without imposing survival.
-/

open MeasureTheory

namespace ThesisSpeed

/-- The offspring-slot mark of the thesis: slot `i` holds `some x` when the
`i`th optional child is present at displacement `x`, and `none` otherwise. -/
abbrev WeightedBranchingStep := BranchingStep ℕ ℝ

/-- Displacement of child slot `i`, whether or not that slot is present. -/
def offspringStep (ξ : WeightedBranchingStep) (i : ℕ) : ℝ :=
  branchingStepIncrement ξ i

def firstDisplacement (ξ : WeightedBranchingStep) : ℝ := offspringStep ξ 0

def childPresent (i : ℕ) : Set WeightedBranchingStep :=
  {ξ | branchingStepPresent ξ i}

theorem childPresent_measurable (i : ℕ) :
    MeasurableSet (childPresent i) :=
  branchingStepPresent_measurableSet i

theorem offspringStep_measurable (i : ℕ) :
    Measurable (fun ξ : WeightedBranchingStep => offspringStep ξ i) :=
  branchingStepIncrement_measurable i

/-- The offspring point process has at least one realized atom. This is a
property of a mark, not part of the ambient mark type. -/
def offspringNonempty : Set WeightedBranchingStep :=
  {ξ | ∃ i : ℕ, ξ ∈ childPresent i}

theorem offspringNonempty_measurable : MeasurableSet offspringNonempty := by
  have hset : offspringNonempty = ⋃ i : ℕ, childPresent i := by
    ext ξ
    simp [offspringNonempty]
  rw [hset]
  exact MeasurableSet.iUnion childPresent_measurable

/-- The offspring point process has at least two distinct realized children. -/
def twoChildren : Set WeightedBranchingStep :=
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
def keepSecond (M : ℝ) : Set WeightedBranchingStep :=
  {ξ | ξ ∈ childPresent 1 ∧ offspringStep ξ 1 ≤ M}

theorem keepSecond_measurable (M : ℝ) : MeasurableSet (keepSecond M) := by
  change MeasurableSet
    (childPresent 1 ∩ {ξ : WeightedBranchingStep | offspringStep ξ 1 ∈ Set.Iic M})
  exact (childPresent_measurable 1).inter
    ((offspringStep_measurable 1) measurableSet_Iic)

/-- The fully truncated law keeps the first child only when it exists and
its displacement is at most `M`. Unlike the backbone law, this can discard
every child. -/
def keepFirst (M : ℝ) : Set WeightedBranchingStep :=
  {ξ | ξ ∈ childPresent 0 ∧ offspringStep ξ 0 ≤ M}

theorem keepFirst_measurable (M : ℝ) : MeasurableSet (keepFirst M) := by
  change MeasurableSet
    (childPresent 0 ∩ {ξ : WeightedBranchingStep | offspringStep ξ 0 ∈ Set.Iic M})
  exact (childPresent_measurable 0).inter
    ((offspringStep_measurable 0) measurableSet_Iic)

noncomputable def retainedChildrenCount (M : ℝ) (ξ : WeightedBranchingStep) : ℕ := by
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

theorem retainedChildrenCount_le_two (M : ℝ) (ξ : WeightedBranchingStep) :
    retainedChildrenCount M ξ ≤ 2 := by
  classical
  unfold retainedChildrenCount
  split_ifs <;> omega

/-- Number of children in the fully truncated law `Ξ⁽ᴹ⁾`; it can be zero. -/
noncomputable def truncatedChildrenCount (M : ℝ)
    (ξ : WeightedBranchingStep) : ℕ := by
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

theorem truncatedChildrenCount_le_two (M : ℝ) (ξ : WeightedBranchingStep) :
    truncatedChildrenCount M ξ ≤ 2 := by
  classical
  unfold truncatedChildrenCount
  split_ifs <;> omega

end ThesisSpeed
