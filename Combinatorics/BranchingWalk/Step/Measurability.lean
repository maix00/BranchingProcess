/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable slot conditions

A branching step is the abstract `Step ι X`: slot `i` holds `some x` when
the corresponding child is present, and `none` otherwise. The support records
the present slots, so nonemptiness and splitting can be expressed directly
through `survive`.

This module derives the measurable sets used. The generic
support events work for any countable slot type. The threshold-selection
rules are also slot-independent: `keepAt` keeps a survive slot below a
threshold, and `keepAbove` is its order-dual counterpart. Their thresholds
are arbitrary, and the measurability of the threshold set is an explicit
hypothesis discharged by the real line with `measurableSet_Iic` and
`measurableSet_Ici`.

## Public declarations

- `nonemptySupport` and `nontrivialSupport` satisfy
  `\(\xi\in nonemptySupport\iff\exists i,\operatorname{survive}(\xi,i)\)`
  and
  `\(\xi\in nontrivialSupport\iff\exists i\ne j,
  \operatorname{survive}(\xi,i)\land\operatorname{survive}(\xi,j)\)`.
  Their measurability results for countable slots are
  `nonemptySupport_measurable` and `nontrivialSupport_measurable`.
- `keepRel R i M` satisfies
  `\(\xi\in keepRel(R,i,M)\iff
  \exists x,\xi(i)=\operatorname{some}(x)\land R(x,M)\)`;
  `keepRel_measurable` assumes the section `{x | R x M}` measurable.
- `keepAt i M` and `keepAbove i M` satisfy
  `\(\xi\in keepAt(i,M)\iff\exists x,\xi(i)=\operatorname{some}(x)
  \land x\le M\)` and
  `\(\xi\in keepAbove(i,M)\iff\exists x,\xi(i)=\operatorname{some}(x)
  \land M\le x\)`. Their measurability results are
  `keepAt_measurable` and `keepAbove_measurable`, and
  `mem_keepAbove_iff_orderDual` identifies the upper event with the lower
  event on `OrderDual X`.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics

namespace Branching

/-- Steps whose support is nonempty, equivalently steps with at least one
survive slot. -/
def nonemptySupport {ι X : Type*} : Set (Step ι X) :=
  {ξ | ∃ i : ι, survive ξ i}

theorem nonemptySupport_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X] :
    MeasurableSet (nonemptySupport (ι := ι) (X := X)) := by
  have hset : nonemptySupport (ι := ι) (X := X) =
      ⋃ i : ι, {ξ : Step ι X | survive ξ i} := by
    ext ξ
    simp [nonemptySupport]
  rw [hset]
  exact MeasurableSet.iUnion fun i => survive_measurableSet i

/-- Steps whose support is nontrivial, equivalently steps with at least two
distinct survive slots. -/
def nontrivialSupport {ι X : Type*} : Set (Step ι X) :=
  {ξ | ∃ i j : ι, i ≠ j ∧ survive ξ i ∧ survive ξ j}

theorem nontrivialSupport_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X] :
    MeasurableSet (nontrivialSupport (ι := ι) (X := X)) := by
  have hset : nontrivialSupport (ι := ι) (X := X) =
      ⋃ i : ι, ⋃ j : ι,
        {ξ : Step ι X | i ≠ j ∧ survive ξ i ∧ survive ξ j} := by
    ext ξ
    simp [nontrivialSupport]
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hset2 : {ξ : Step ι X | i ≠ j ∧ survive ξ i ∧ survive ξ j} =
        {ξ : Step ι X | survive ξ i} ∩ {ξ : Step ι X | survive ξ j} := by
      ext ξ
      constructor
      · rintro ⟨_, hi, hj⟩
        exact ⟨hi, hj⟩
      · rintro ⟨hi, hj⟩
        exact ⟨hij, hi, hj⟩
    rw [hset2]
    exact (survive_measurableSet i).inter (survive_measurableSet j)

/-- Keep a slot when its present mark satisfies an arbitrary relation with
the threshold. The slot is an explicit parameter, so no numerical indexing is
built into the rule. -/
def keepRel {ι X : Type*}
    (R : X → X → Prop) (i : ι) (M : X) : Set (Step ι X) :=
  (fun ξ : Step ι X => ξ i) ⁻¹' (some '' {x : X | R x M})

theorem keepRel_measurable {ι X : Type*}
    [MeasurableSpace X]
    (R : X → X → Prop) (i : ι) (M : X)
    (hM : MeasurableSet {x : X | R x M}) :
    MeasurableSet (keepRel R i M) := by
  exact (measurable_pi_apply i) (measurableSet_option_some_image hM)

/-- Keep a survive slot when its value is at most `M`. -/
def keepAt {ι X : Type*} [LE X]
    (i : ι) (M : X) : Set (Step ι X) :=
  keepRel (· ≤ ·) i M

theorem keepAt_measurable {ι X : Type*}
    [LE X] [MeasurableSpace X]
    (i : ι) (M : X) (hM : MeasurableSet {x : X | x ≤ M}) :
    MeasurableSet (keepAt i M) := by
  exact keepRel_measurable (· ≤ ·) i M hM

/-- The order-dual counterpart of `keepAt`: keep a survive slot when its
value is at least `M`. -/
def keepAbove {ι X : Type*} [LE X]
    (i : ι) (M : X) : Set (Step ι X) :=
  keepRel (fun x M' => M' ≤ x) i M

theorem keepAbove_measurable {ι X : Type*}
    [LE X] [MeasurableSpace X]
    (i : ι) (M : X) (hM : MeasurableSet {x : X | M ≤ x}) :
    MeasurableSet (keepAbove i M) := by
  exact keepRel_measurable (fun x M' => M' ≤ x) i M hM

/-- Left-right symmetry of the threshold rule: the upper rule is the lower
rule after reversing the order on the values. -/
theorem mem_keepAbove_iff_orderDual {ι X : Type*}
    [LE X] (i : ι) (M : X) (ξ : Step ι X) :
    ξ ∈ keepAbove i M ↔
      (fun j => (ξ j).map OrderDual.toDual) ∈
        keepAt (X := OrderDual X) i (OrderDual.toDual M) := by
  cases h : ξ i with
  | none =>
      simp [keepAbove, keepAt, keepRel, h]
  | some x =>
      simp [keepAbove, keepAt, keepRel, h,
        OrderDual.toDual_le_toDual]

end Branching

end Combinatorics

end
