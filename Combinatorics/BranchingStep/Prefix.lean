import Combinatorics.BranchingStep.Basic

/-!
# Order conditions on the present slots of a branching step

The order condition is parameterized by an explicit relation, so an
increasing and a decreasing enumeration are two instances of one definition
and the condition is left--right symmetric; `branchingStepPrefixRel_optionMap_iff`
is the transport lemma and `branchingStepPrefixAntitone_iff_orderDual` reads
the decreasing case in the dual order. `OrderedBranchingStep` conjoins the
presence prefix with the increasing order condition.
-/

namespace BranchingStep

/-- The slots present in `ξ` are listed in the order prescribed by the binary
relation `rel`: an earlier slot never compares above a later one. The relation
is an explicit parameter, so the increasing and the decreasing enumeration of
the same step are two instances of one definition rather than two separate
constructions. This is what makes the condition left--right symmetric; the
order-dual form is `branchingStepPrefixRel_optionMap_iff`. -/
def branchingStepPrefixRel {ι X : Type*} [LT ι]
    (rel : X → X → Prop) (ξ : BranchingStep ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → rel x y

/-- The increasing case of `branchingStepPrefixRel`, used by the thesis's
left-to-right optional-slot enumeration. -/
def branchingStepPrefixOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPrefixRel (· ≤ ·) ξ

/-- The decreasing mirror image of `branchingStepPrefixOrdered`. -/
def branchingStepPrefixAntitone {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPrefixRel (fun x y => y ≤ x) ξ

/-- Left--right symmetry of the ordering condition, in the form used by the
thesis: transporting a step along an order embedding turns the condition for
one relation into the condition for the other. Reversing the order on the
marks (`e = OrderDual.toDual`) is the instance that swaps "from the left" and
"from the right"; no direction is singled out by the definition. -/
theorem branchingStepPrefixRel_optionMap_iff {ι X Y : Type*} [LT ι]
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (e : X → Y)
    (he : ∀ a b, rel' (e a) (e b) ↔ rel a b) (ξ : BranchingStep ι X) :
    branchingStepPrefixRel rel' (fun i => (ξ i).map e) ↔
      branchingStepPrefixRel rel ξ := by
  constructor
  · intro h i j x y hij hx hy
    exact (he x y).1 (h i j (e x) (e y) hij
      (by simp [hx]) (by simp [hy]))
  · intro h i j x y hij hx hy
    rcases Option.map_eq_some_iff.1 hx with ⟨a, ha, rfl⟩
    rcases Option.map_eq_some_iff.1 hy with ⟨b, hb, rfl⟩
    exact (he a b).2 (h i j a b hij ha hb)

/-- The decreasing version is the increasing version read in the dual order. -/
theorem branchingStepPrefixAntitone_iff_orderDual {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) :
    branchingStepPrefixAntitone ξ ↔
      branchingStepPrefixOrdered (X := OrderDual X)
        (fun i => (ξ i).map OrderDual.toDual) := by
  exact (branchingStepPrefixRel_optionMap_iff (fun x y : X => y ≤ x) (· ≤ ·)
    OrderDual.toDual (fun a b => OrderDual.toDual_le_toDual) ξ).symm

def branchingStepPresencePrefix {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

def OrderedBranchingStep {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPresencePrefix ξ ∧ branchingStepPrefixOrdered ξ
theorem branchingStep_present_of_later
    {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X)
    (hprefix : branchingStepPresencePrefix ξ)
    {i j : ι} (hij : i < j) (h : branchingStepPresent ξ j) :
    branchingStepPresent ξ i := by
  classical
  by_contra hi
  simp only [branchingStepPresent, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simpa [hxi]
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hprefix i j hij hnone
  rw [hy] at hjnone
  cases hjnone
/-- A later present slot forces every earlier slot to be present, stated for
the non-strict order so that `i = j` needs no separate case. -/
theorem branchingStep_present_of_le
    {ι X : Type*} [PartialOrder ι]
    (ξ : BranchingStep ι X)
    (hprefix : branchingStepPresencePrefix ξ)
    {i j : ι} (hij : i ≤ j) (h : branchingStepPresent ξ j) :
    branchingStepPresent ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · exact branchingStep_present_of_later ξ hprefix hlt h

end BranchingStep
