import ThesisSpeed.Probability.PointProcess.Basic

/-!
# Legacy weighted-slot encoding

This module is retained only while the old branching and stopping arguments
are migrated to `BranchingStep`.  Every child slot has a real presence flag
and a real displacement; it is
present exactly when the flag is positive. Thus the empty point process is
represented by a mark whose flags are all nonpositive. This encodes finite
and countably infinite offspring without imposing survival.
-/

open MeasureTheory

namespace ThesisSpeed

abbrev OffspringMark := ℕ → ℝ × ℝ

/-! The first component is the realization/weight flag and the second is the
one-step displacement.  These names distinguish a slot increment from a
path's accumulated mark. -/
def offspringStep (ξ : OffspringMark) (i : ℕ) : ℝ := (ξ i).2

def firstDisplacement (ξ : OffspringMark) : ℝ := (ξ 0).2

def childPresent (i : ℕ) : Set OffspringMark :=
  {ξ | 0 < (ξ i).1}

theorem childPresent_measurable (i : ℕ) :
    MeasurableSet (childPresent i) := by
  change MeasurableSet {ξ : OffspringMark | (ξ i).1 ∈ Set.Ioi (0 : ℝ)}
  exact ((measurable_pi_apply i).fst) measurableSet_Ioi

/-- The offspring point process has at least one realized atom. This is a
property of a mark, not part of the ambient mark type. -/
def offspringNonempty : Set OffspringMark :=
  {ξ | ∃ i : ℕ, ξ ∈ childPresent i}

theorem offspringNonempty_measurable : MeasurableSet offspringNonempty := by
  have hset : offspringNonempty = ⋃ i : ℕ, childPresent i := by
    ext ξ
    simp [offspringNonempty]
  rw [hset]
  exact MeasurableSet.iUnion childPresent_measurable

/-- The offspring point process has at least two distinct realized children. -/
def twoChildren : Set OffspringMark :=
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
def keepSecond (M : ℝ) : Set OffspringMark :=
  {ξ | ξ ∈ childPresent 1 ∧ (ξ 1).2 ≤ M}

theorem keepSecond_measurable (M : ℝ) : MeasurableSet (keepSecond M) := by
  change MeasurableSet
    (childPresent 1 ∩ {ξ : OffspringMark | (ξ 1).2 ∈ Set.Iic M})
  exact (childPresent_measurable 1).inter
    ((measurable_pi_apply 1).snd measurableSet_Iic)

/-- The fully truncated law keeps the first child only when it exists and
its displacement is at most `M`. Unlike the backbone law, this can discard
every child. -/
def keepFirst (M : ℝ) : Set OffspringMark :=
  {ξ | ξ ∈ childPresent 0 ∧ (ξ 0).2 ≤ M}

theorem keepFirst_measurable (M : ℝ) : MeasurableSet (keepFirst M) := by
  change MeasurableSet
    (childPresent 0 ∩ {ξ : OffspringMark | (ξ 0).2 ∈ Set.Iic M})
  exact (childPresent_measurable 0).inter
    ((measurable_pi_apply 0).snd measurableSet_Iic)

noncomputable def retainedChildrenCount (M : ℝ) (ξ : OffspringMark) : ℕ := by
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

theorem retainedChildrenCount_le_two (M : ℝ) (ξ : OffspringMark) :
    retainedChildrenCount M ξ ≤ 2 := by
  classical
  unfold retainedChildrenCount
  split_ifs <;> omega

/-- Number of children in the fully truncated law `Ξ⁽ᴹ⁾`; it can be zero. -/
noncomputable def truncatedChildrenCount (M : ℝ)
    (ξ : OffspringMark) : ℕ := by
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

theorem truncatedChildrenCount_le_two (M : ℝ) (ξ : OffspringMark) :
    truncatedChildrenCount M ξ ≤ 2 := by
  classical
  unfold truncatedChildrenCount
  split_ifs <;> omega

end ThesisSpeed
