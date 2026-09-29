module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Relations on sibling marks

The order condition is parameterized by an explicit relation, so an
increasing and a decreasing enumeration are two instances of one definition
and the condition is left--right symmetric; `siblingRel_optionMap_iff` is the
transport lemma. The increasing and decreasing cases live in `Monotone.lean`.

Presence closure and relabeling are separate interfaces in
`SiblingClosed.lean` and `SiblingClosable.lean`; keeping them out of this file
means a consumer asking only about relations does not acquire either closure
or choice principles.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- The slots survive in `ξ` are listed in the order prescribed by the binary
relation `rel`: an earlier slot never compares above a later one. The relation
is an explicit parameter, so the increasing and the decreasing enumeration of
the same step are two instances of one definition rather than two separate
constructions. This is what makes the condition left--right symmetric; the
order-dual form is `siblingRel_optionMap_iff`. -/
def siblingRel {ι X : Type*} [LT ι]
    (rel : X → X → Prop) (ξ : Step ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → rel x y

/-- Left--right symmetry of the ordering condition, in the form used by the
thesis: transporting a step along an order embedding turns the condition for
one relation into the condition for the other. Reversing the order on the
marks (`e = OrderDual.toDual`) is the instance that swaps "from the left" and
"from the right"; no direction is singled out by the definition. -/
theorem siblingRel_optionMap_iff {ι X Y : Type*} [LT ι]
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (e : X → Y)
    (he : ∀ a b, rel' (e a) (e b) ↔ rel a b) (ξ : Step ι X) :
    siblingRel rel' (fun i => (ξ i).map e) ↔
      siblingRel rel ξ := by
  constructor
  · intro h i j x y hij hx hy
    exact (he x y).1 (h i j (e x) (e y) hij
      (by simp [hx]) (by simp [hy]))
  · intro h i j x y hij hx hy
    rcases Option.map_eq_some_iff.1 hx with ⟨a, ha, rfl⟩
    rcases Option.map_eq_some_iff.1 hy with ⟨b, hb, rfl⟩
    exact (he a b).2 (h i j a b hij ha hb)

end Branching

end Combinatorics

end
