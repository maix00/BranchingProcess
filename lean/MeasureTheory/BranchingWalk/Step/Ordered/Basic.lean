import MeasureTheory.BranchingWalk.Step.Relation

/-!
# Ordered branching steps

`parentOrdered` is the increasing case of `parentRel`, and `parentAntitone`
is its decreasing mirror image.  `presenceParent` says that the present slots
form an initial segment of the slot order; together they make an
`OrderedStep`.  The monotonicity of the zero-defaulted value sits here because
it uses this order condition.

`orderedStepsOf` collects the steps satisfying a relation-ordered condition,
so the thesis's left-to-right enumeration is the instance `orderedSteps` and
its decreasing mirror is `antitoneSteps`.  The measurability of both instances
is in `Step/Ordered/Measurability.lean`.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- The increasing case of `parentRel`, used by the thesis's
left-to-right optional-slot enumeration. -/
def parentOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  parentRel (· ≤ ·) ξ

/-- The decreasing mirror image of `parentOrdered`. -/
def parentAntitone {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  parentRel (fun x y => y ≤ x) ξ

/-- The decreasing version is the increasing version read in the dual order. -/
theorem parentAntitone_iff_orderDual {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    parentAntitone ξ ↔
      parentOrdered (X := OrderDual X)
        (fun i => (ξ i).map OrderDual.toDual) := by
  exact (parentRel_optionMap_iff (fun x y : X => y ≤ x) (· ≤ ·)
    OrderDual.toDual (fun a b => OrderDual.toDual_le_toDual) ξ).symm

/-- The present slots of a step form an initial segment of the slot order:
an absent slot cannot be followed by a present one. -/
def presenceParent {ι X : Type*} [LT ι]
    (ξ : Step ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

/-- An ordered step: absence is parent-closed and the present marks are
increasing in the slot order. -/
def OrderedStep {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  presenceParent ξ ∧ parentOrdered ξ

/-- The present slots of a step are listed from the left. -/
abbrev OrderedNatStep {X : Type*} [LE X] (ξ : NatStep X) : Prop :=
  OrderedStep ξ

/-- The paper's ordered real-valued branching step. -/
abbrev OrderedNatRealStep (ξ : NatRealStep) : Prop := OrderedNatStep ξ

theorem present_of_later
    {ι X : Type*} [LT ι]
    (ξ : Step ι X)
    (hparent : presenceParent ξ)
    {i j : ι} (hij : i < j) (h : present ξ j) :
    present ξ i := by
  classical
  by_contra hi
  simp only [present, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simp
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hparent i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- A later present slot forces every earlier slot to be present, stated for
the non-strict order so that `i = j` needs no separate case. -/
theorem present_of_le
    {ι X : Type*} [PartialOrder ι]
    (ξ : Step ι X)
    (hparent : presenceParent ξ)
    {i j : ι} (hij : i ≤ j) (h : present ξ j) :
    present ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · exact present_of_later ξ hparent hlt h

theorem value'_mono_of_present
    {ι X : Type*} [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hordered : parentOrdered ξ)
    {i j : ι} (hij : i ≤ j)
    (hi : present ξ i) (hj : present ξ j) :
    value' ξ i ≤ value' ξ j := by
  rcases hi with ⟨x, hx⟩
  rcases hj with ⟨y, hy⟩
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij heq
    rw [value'_some ξ i x hx, value'_some ξ j y hy]
    exact hordered i j x y hlt hx hy

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

/-- Steps whose present slots form a parent-closed initial segment and whose
present marks satisfy `rel` in increasing slot order. -/
def orderedStepsOf {ι X : Type*} [LT ι]
    (rel : X → X → Prop) : Set (Step ι X) :=
  {ξ | presenceParent ξ ∧ parentRel rel ξ}

/-- The increasing simultaneous enumeration of the optional children. -/
def orderedSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (· ≤ ·)

/-- The decreasing mirror image of `orderedSteps`. -/
def antitoneSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (fun x y => y ≤ x)

theorem mem_orderedSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ orderedSteps ↔ OrderedStep ξ := Iff.rfl

theorem mem_antitoneSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ antitoneSteps ↔ presenceParent ξ ∧ parentAntitone ξ := Iff.rfl

/-- Under the ordering condition, a present later slot forces every earlier
slot to be present. -/
theorem orderedSteps_present_of_le {ι X : Type*}
    [PartialOrder ι] [LE X] (ξ : Step ι X)
    (hξ : ξ ∈ orderedSteps) {i j : ι} (hij : i ≤ j)
    (hj : present ξ j) :
    present ξ i :=
  present_of_le ξ hξ.1 hij hj

/-- Optional child values are nondecreasing along the enumeration. -/
theorem orderedSteps_value_mono {ι X : Type*}
    [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hξ : ξ ∈ orderedSteps) {i j : ι}
    (hij : i ≤ j) (hj : present ξ j) :
    value' ξ i ≤ value' ξ j :=
  value'_mono_of_present ξ hξ.2 hij
    (present_of_le ξ hξ.1 hij hj) hj

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : NatRealStep :=
  fun i => if i = 0 then some 1 else if i = 1 then some 0 else none

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedSteps := by
  intro h
  have hone : present unorderedExample 1 := by
    simp [unorderedExample, present]
  have hle : value' unorderedExample 0 ≤
      value' unorderedExample 1 :=
    orderedSteps_value_mono unorderedExample h
      (Nat.zero_le 1) hone
  norm_num [unorderedExample, value'] at hle

end BranchingWalk

end MeasureTheory
