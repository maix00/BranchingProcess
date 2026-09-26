import MeasureTheory.BranchingWalk.Step.Value
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The child-slot vocabulary

The thesis's branching step is the abstract `Step ℕ X`: slot `i` holds
`some x` when the `i`th optional child is present at displacement `x`, and
`none` otherwise. The slot labels are `ℕ` because the paper enumerates the
children of a node from the left; the value type is arbitrary, and the
paper's real displacements are the specialization `NatRealStep`.

A slot is present exactly when it holds a child, so the empty child point
process is the all-absent step; this encodes finite and countably infinite
child sets without imposing survival. The module collects the slot
vocabulary used by the paper's arguments (`Ξ₁`, `Ξ₂`, ...): presence of a
labelled child, nonemptiness, the causal `keepSecond` rule, the fully
truncated `keepFirst` rule, and their child counts.

The rules only compare a slot value with a threshold `M`, so they are stated
for an arbitrary value type with a zero and an order; the measurability of a
threshold set is carried by the explicit hypothesis
`MeasurableSet {x : X | x ≤ M}`, which the real line discharges by
`measurableSet_Iic`.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

/-- A branching step whose slots are labelled by `ℕ`: the paper's optional
enumeration of the children of one node, with arbitrary slot values. -/
abbrev NatStep (X : Type*) := Step ℕ X

/-- The paper's branching step: `ℕ`-labelled optional children at real
displacements. -/
abbrev NatRealStep := NatStep ℝ

/-- The present slots of a step are listed from the left. -/
abbrev OrderedNatStep {X : Type*} [LE X] (ξ : NatStep X) : Prop :=
  OrderedStep ξ

/-- The paper's ordered real-valued branching step. -/
abbrev OrderedNatRealStep (ξ : NatRealStep) : Prop := OrderedNatStep ξ

/-- The set of steps in which slot `i` holds a child. -/
def childPresent {X : Type*} (i : ℕ) : Set (NatStep X) :=
  {ξ | present ξ i}

theorem childPresent_measurable {X : Type*} [MeasurableSpace X] (i : ℕ) :
    MeasurableSet (childPresent (X := X) i) :=
  present_measurableSet i

/-- The child point process has at least one realized atom. This is a
property of a mark, not part of the ambient mark type. -/
def childNonempty {X : Type*} : Set (NatStep X) :=
  {ξ | ∃ i : ℕ, ξ ∈ childPresent i}

theorem childNonempty_measurable {X : Type*} [MeasurableSpace X] :
    MeasurableSet (childNonempty (X := X)) := by
  have hset : childNonempty (X := X) = ⋃ i : ℕ, childPresent i := by
    ext ξ
    simp [childNonempty]
  rw [hset]
  exact MeasurableSet.iUnion childPresent_measurable

/-- The child point process has at least two distinct realized children. -/
def twoChildren {X : Type*} : Set (NatStep X) :=
  {ξ | ∃ i j : ℕ, i ≠ j ∧ ξ ∈ childPresent i ∧ ξ ∈ childPresent j}

theorem twoChildren_measurable {X : Type*} [MeasurableSpace X] :
    MeasurableSet (twoChildren (X := X)) := by
  have hset : twoChildren (X := X) =
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
second only if it exists and its value is at most `M`. -/
def keepSecond {X : Type*} [Zero X] [LE X] (M : X) : Set (NatStep X) :=
  {ξ | ξ ∈ childPresent 1 ∧ value ξ 1 ≤ M}

theorem keepSecond_measurable {X : Type*} [Zero X] [LE X] [MeasurableSpace X]
    (M : X) (hM : MeasurableSet {x : X | x ≤ M}) :
    MeasurableSet (keepSecond M) := by
  change MeasurableSet
    (childPresent (X := X) 1 ∩ {ξ : NatStep X | value ξ 1 ≤ M})
  exact (childPresent_measurable 1).inter ((value_measurable 1) hM)

/-- The fully truncated law keeps the first child only when it exists and
its value is at most `M`. Unlike the backbone law, this can discard every
child. -/
def keepFirst {X : Type*} [Zero X] [LE X] (M : X) : Set (NatStep X) :=
  {ξ | ξ ∈ childPresent 0 ∧ value ξ 0 ≤ M}

theorem keepFirst_measurable {X : Type*} [Zero X] [LE X] [MeasurableSpace X]
    (M : X) (hM : MeasurableSet {x : X | x ≤ M}) :
    MeasurableSet (keepFirst M) := by
  change MeasurableSet
    (childPresent (X := X) 0 ∩ {ξ : NatStep X | value ξ 0 ≤ M})
  exact (childPresent_measurable 0).inter ((value_measurable 0) hM)

/-- Children retained by the causal one-or-two-child rule: the first child
whenever it exists, plus the second when `keepSecond M` accepts it. -/
noncomputable def retainedChildrenCount {X : Type*} [Zero X] [LE X]
    (M : X) (ξ : NatStep X) : ℕ := by
  classical
  exact (if ξ ∈ childPresent 0 then 1 else 0) +
    (if ξ ∈ keepSecond M then 1 else 0)

theorem retainedChildrenCount_measurable {X : Type*}
    [Zero X] [LE X] [MeasurableSpace X]
    (M : X) (hM : MeasurableSet {x : X | x ≤ M}) :
    Measurable (retainedChildrenCount M) := by
  classical
  unfold retainedChildrenCount
  exact ((measurable_const).ite (childPresent_measurable 0)
    measurable_const).add
      ((measurable_const).ite (keepSecond_measurable M hM) measurable_const)

theorem retainedChildrenCount_le_two {X : Type*} [Zero X] [LE X]
    (M : X) (ξ : NatStep X) :
    retainedChildrenCount M ξ ≤ 2 := by
  classical
  unfold retainedChildrenCount
  split_ifs <;> omega

/-- Number of children in the fully truncated law `Ξ⁽ᴹ⁾`; it can be zero. -/
noncomputable def truncatedChildrenCount {X : Type*} [Zero X] [LE X]
    (M : X) (ξ : NatStep X) : ℕ := by
  classical
  exact (if ξ ∈ keepFirst M then 1 else 0) +
    (if ξ ∈ keepSecond M then 1 else 0)

theorem truncatedChildrenCount_measurable {X : Type*}
    [Zero X] [LE X] [MeasurableSpace X]
    (M : X) (hM : MeasurableSet {x : X | x ≤ M}) :
    Measurable (truncatedChildrenCount M) := by
  classical
  unfold truncatedChildrenCount
  exact ((measurable_const).ite (keepFirst_measurable M hM)
    measurable_const).add
      ((measurable_const).ite (keepSecond_measurable M hM) measurable_const)

theorem truncatedChildrenCount_le_two {X : Type*} [Zero X] [LE X]
    (M : X) (ξ : NatStep X) :
    truncatedChildrenCount M ξ ≤ 2 := by
  classical
  unfold truncatedChildrenCount
  split_ifs <;> omega

theorem orderedNatStep_support_initial {X : Type*} [LE X]
    (ξ : NatStep X) (hξ : OrderedNatStep ξ)
    {i j : ℕ} (hij : i < j) (hj : present ξ j) :
    present ξ i :=
  present_of_later ξ hξ.1 hij hj

theorem orderedNatStep_support_bounded {X : Type*} [LE X]
    (ξ : NatStep X) (_hξ : OrderedNatStep ξ)
    (hfinite : (support ξ).Finite) :
    ∃ n, ∀ i, present ξ i → i < n := by
  classical
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  refine ⟨n + 1, ?_⟩
  intro i hi
  exact lt_of_le_of_lt (hn hi) (Nat.lt_succ_self n)

end BranchingWalk

end MeasureTheory
