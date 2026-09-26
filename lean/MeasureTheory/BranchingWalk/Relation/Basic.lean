import MeasureTheory.BranchingWalk.Step.Basic

/-!
# Relations on the present slots of a branching step

The order condition is parameterized by an explicit relation, so an
increasing and a decreasing enumeration are two instances of one definition
and the condition is left--right symmetric; `parentRel_optionMap_iff` is the
transport lemma.  The increasing and decreasing cases, and the presence
condition that makes a step ordered, live in `Ordered.lean`.

`presenceParent` is the closure condition that is independent of any order on
the marks: the present slots form an initial segment. It is grouped here with
`parentRel` because both speak only of which slots are present, not of their
mark values.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- The slots present in `ξ` are listed in the order prescribed by the binary
relation `rel`: an earlier slot never compares above a later one. The relation
is an explicit parameter, so the increasing and the decreasing enumeration of
the same step are two instances of one definition rather than two separate
constructions. This is what makes the condition left--right symmetric; the
order-dual form is `parentRel_optionMap_iff`. -/
def parentRel {ι X : Type*} [LT ι]
    (rel : X → X → Prop) (ξ : Step ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → rel x y

/-- Left--right symmetry of the ordering condition, in the form used by the
thesis: transporting a step along an order embedding turns the condition for
one relation into the condition for the other. Reversing the order on the
marks (`e = OrderDual.toDual`) is the instance that swaps "from the left" and
"from the right"; no direction is singled out by the definition. -/
theorem parentRel_optionMap_iff {ι X Y : Type*} [LT ι]
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (e : X → Y)
    (he : ∀ a b, rel' (e a) (e b) ↔ rel a b) (ξ : Step ι X) :
    parentRel rel' (fun i => (ξ i).map e) ↔
      parentRel rel ξ := by
  constructor
  · intro h i j x y hij hx hy
    exact (he x y).1 (h i j (e x) (e y) hij
      (by simp [hx]) (by simp [hy]))
  · intro h i j x y hij hx hy
    rcases Option.map_eq_some_iff.1 hx with ⟨a, ha, rfl⟩
    rcases Option.map_eq_some_iff.1 hy with ⟨b, hb, rfl⟩
    exact (he a b).2 (h i j a b hij ha hb)

/-- The present slots of a step form an initial segment of the slot order:
an absent slot cannot be followed by a present one. -/
def presenceParent {ι X : Type*} [LT ι]
    (ξ : Step ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

end BranchingWalk

end MeasureTheory
