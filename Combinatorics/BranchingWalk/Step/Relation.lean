import Combinatorics.BranchingWalk.Step.Basic

/-!
# Relations on the survive slots of a branching step

The order condition is parameterized by an explicit relation, so an
increasing and a decreasing enumeration are two instances of one definition
and the condition is left--right symmetric; `siblingRel_optionMap_iff` is the
transport lemma.  The increasing and decreasing cases, and the presence
condition that makes a step ordered, live in `Ordered.lean`.

`IsSiblingClosed` is the closure condition that is independent of any order on
the marks: an absent slot forces every larger slot absent, so the surviving slots
form an initial segment and the absent ones a final segment. It is grouped
here with `siblingRel` because both speak only of which slots are survive, not
of their mark values, and its consequences — a survive slot forces every earlier
slot to be survive — are stated here for the same reason.
-/

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

/-- The survive slots of a step form an initial segment of the slot order:
an absent slot cannot be followed by a survive one. -/
def Step.IsSiblingClosed {ι X : Type*} [LT ι]
    (ξ : Step ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

/-- A survive slot forces every earlier slot to be survive: an absent slot forces every larger slot to be
absent, so the survive slots are closed downwards, and a slot below a survive one is itself survive. -/
theorem Step.IsSiblingClosed.survive_of_lt {ι X : Type*} [LT ι] {ξ : Step ι X}
    (h : Step.IsSiblingClosed ξ) {i j : ι} (hij : i < j) (hj : survive ξ j) : survive ξ i := by
  classical
  by_contra hi
  simp only [survive, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simp
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := hj
  have hjnone := h i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- The same at the non-strict slot order, so that the case `i = j` needs no separate treatment. -/
theorem Step.IsSiblingClosed.survive_of_le {ι X : Type*} [PartialOrder ι] {ξ : Step ι X}
    (h : Step.IsSiblingClosed ξ) {i j : ι} (hij : i ≤ j) (hj : survive ξ j) : survive ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hj
  · exact h.survive_of_lt hlt hj

section IsSiblingClosable

variable {ι X : Type*} [LT ι]

/-- On a countably infinite slot type every infinite set of slots carries an injection of the slot type:
`ℕ ↪ T` composed with `ι ↪ ℕ`. This is the one size argument behind sibling closability. -/
theorem exists_injective_range_subset_of_infinite {ι : Type*} [Countable ι] {T : Set ι}
    (hT : T.Infinite) :
    ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ T := by
  obtain ⟨g, hg⟩ := (exists_injective_nat ι : ∃ g : ι → ℕ, Function.Injective g)
  let e : ℕ ↪ ↥T := hT.natEmbedding
  exact ⟨fun i => (e (g i) : ι), fun i j hij => hg (e.injective (Subtype.coe_injective hij)),
    by rintro _ ⟨i, rfl⟩; exact (e (g i)).2⟩

/-- A step is sibling closable when an injective relabeling of its slots turns it into a step whose
surviving slots form an initial segment. The relabeling acts as a pullback, carrying the support to
`f ⁻¹' support ξ`, and no surjectivity is asked of it. -/
class Step.IsSiblingClosable (ξ : Step ι X) : Prop where
  exists_relabel :
  ∃ f : ι → ι, Function.Injective f ∧ Step.IsSiblingClosed fun i => ξ (f i)

/-- A step is sibling closable as soon as an injection of the slot type lands inside its surviving
slots: the relabeled step then survives everywhere, and every absent slot of it is contradicted by the
surviving one below it. -/
theorem Step.isSiblingClosable_of_range_subset_support {ξ : Step ι X} {f : ι → ι}
    (hf : Function.Injective f) (h : Set.range f ⊆ support ξ) : ξ.IsSiblingClosable :=
  ⟨f, hf, fun i _ _ hi => by
    obtain ⟨y, hy⟩ := h ⟨i, rfl⟩
    exact absurd hi (by simp [hy])⟩

/-- A step is sibling closable as soon as an injection of the slot type lands outside its surviving
slots: the relabeled step then survives nowhere, so it has no surviving slot to contradict. -/
theorem Step.isSiblingClosable_of_range_subset_compl {ξ : Step ι X} {f : ι → ι}
    (hf : Function.Injective f) (h : Set.range f ⊆ (support ξ)ᶜ) : ξ.IsSiblingClosable :=
  ⟨f, hf, fun _ j _ _ => by
    by_contra hc
    exact h ⟨j, rfl⟩ ((survive_iff_ne_none ξ (f j)).mpr hc)⟩

/-- The abstract condition behind the countable case: if every set carries an injection of the slot
type either into itself or into its complement, then every step on that slot type is sibling closable.
No size or countability is assumed; these two are the structural hypotheses. -/
theorem Step.isSiblingClosable_of_forall
    (h : ∀ S : Set ι, (∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ S) ∨
      ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ Sᶜ) (ξ : Step ι X) :
    ξ.IsSiblingClosable := by
  rcases h (support ξ) with ⟨f, hf, hfs⟩ | ⟨f, hf, hfs⟩
  · exact isSiblingClosable_of_range_subset_support hf hfs
  · exact isSiblingClosable_of_range_subset_compl hf hfs

/-- A slot type is sibling closable when every set carries an injection of the slot type either into
itself or into its complement. Indexed by the slot type, so that instance search can find it. -/
class IsSiblingClosable (ι : Type*) [LT ι] : Prop where
  exists_injective_or_compl : ∀ S : Set ι,
    (∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ S) ∨
      ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ Sᶜ

/-- On a closable slot type every step is sibling closable, by instance search. -/
instance (priority := 100) [hι : IsSiblingClosable ι] (ξ : Step ι X) : Step.IsSiblingClosable ξ :=
  Step.isSiblingClosable_of_forall hι.exists_injective_or_compl ξ

/-- A countably infinite slot type is sibling closable: a subset is either infinite, and then `ℕ ↪ S`
composes with `ι ↪ ℕ`, or finite, and then its complement is infinite and the same composition applies.
So `IsSiblingClosable ℕ` is found by instance search and never needs handing in. -/
instance (priority := 100) [Countable ι] [Infinite ι] : IsSiblingClosable ι :=
  ⟨fun S => by
    by_cases hS : S.Infinite
    · exact Or.inl (exists_injective_range_subset_of_infinite hS)
    · exact Or.inr (exists_injective_range_subset_of_infinite (Set.not_infinite.mp hS).infinite_compl)⟩

end IsSiblingClosable

/-- A finite set of slots leaves an infinite complement in a countable infinite slot type, so the slots
outside it receive an injection of the slot type — in particular the slots outside the children of a
finitely supported step, which is where the relabelling onto an initial segment sends them. -/
theorem exists_injective_notMem_of_finite {ι : Type*} [Countable ι] [Infinite ι] {S : Finset ι} :
    ∃ ψ : ι → ι, Function.Injective ψ ∧ ∀ i, ψ i ∉ (↑S : Set ι) := by
  obtain ⟨ψ, hψ, hsub⟩ := exists_injective_range_subset_of_infinite (S.finite_toSet.infinite_compl)
  exact ⟨ψ, hψ, fun i => by simpa using hsub ⟨i, rfl⟩⟩

end Branching

end Combinatorics
