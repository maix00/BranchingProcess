module

public import Combinatorics.BranchingWalk.Step.SiblingClosed

/-!
# Relabelable sibling steps

`Step.IsSiblingClosable` is the optional relabeling property: an injective
pullback of the slot field is sibling-closed. It is deliberately distinct
from `Step.IsSiblingClosed`, which speaks about the original slot order.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

section IsSiblingClosable

variable {ι X : Type*} [LT ι]

/-- Every infinite subset of a countably infinite slot type contains an
injective copy of the slot type. -/
theorem exists_injective_range_subset_of_infinite {ι : Type*} [Countable ι] {T : Set ι}
    (hT : T.Infinite) :
    ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ T := by
  obtain ⟨g, hg⟩ := (exists_injective_nat ι : ∃ g : ι → ℕ, Function.Injective g)
  let e : ℕ ↪ ↥T := hT.natEmbedding
  exact ⟨fun i => (e (g i) : ι), fun i j hij => hg (e.injective (Subtype.coe_injective hij)),
    by rintro _ ⟨i, rfl⟩; exact (e (g i)).2⟩

/-- An injective relabeling makes the surviving slots an initial segment. -/
class Step.IsSiblingClosable (ξ : Step ι X) : Prop where
  exists_relabel :
  ∃ f : ι → ι, Function.Injective f ∧ Step.IsSiblingClosed fun i => ξ (f i)

/-- An injection landing inside the support witnesses sibling closability. -/
theorem Step.isSiblingClosable_of_range_subset_support {ξ : Step ι X} {f : ι → ι}
    (hf : Function.Injective f) (h : Set.range f ⊆ support ξ) : ξ.IsSiblingClosable :=
  ⟨f, hf, fun i _ _ hi => by
    obtain ⟨y, hy⟩ := h ⟨i, rfl⟩
    exact absurd hi (by simp [hy])⟩

/-- An injection landing outside the support witnesses sibling closability. -/
theorem Step.isSiblingClosable_of_range_subset_compl {ξ : Step ι X} {f : ι → ι}
    (hf : Function.Injective f) (h : Set.range f ⊆ (support ξ)ᶜ) : ξ.IsSiblingClosable :=
  ⟨f, hf, fun _ j _ _ => by
    by_contra hc
    exact h ⟨j, rfl⟩ ((survive_iff_ne_none ξ (f j)).mpr hc)⟩

/-- If every set carries an injection into itself or its complement, every step
is sibling closable. -/
theorem Step.isSiblingClosable_of_forall
    (h : ∀ S : Set ι, (∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ S) ∨
      ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ Sᶜ) (ξ : Step ι X) :
    ξ.IsSiblingClosable := by
  rcases h (support ξ) with ⟨f, hf, hfs⟩ | ⟨f, hf, hfs⟩
  · exact isSiblingClosable_of_range_subset_support hf hfs
  · exact isSiblingClosable_of_range_subset_compl hf hfs

/-- A slot type is sibling closable when every set carries an injection into
itself or its complement. -/
class IsSiblingClosable (ι : Type*) [LT ι] : Prop where
  exists_injective_or_compl : ∀ S : Set ι,
    (∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ S) ∨
      ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ Sᶜ

instance (priority := 100) [hι : IsSiblingClosable ι] (ξ : Step ι X) : Step.IsSiblingClosable ξ :=
  Step.isSiblingClosable_of_forall hι.exists_injective_or_compl ξ

/-- A countably infinite slot type is sibling closable. -/
instance (priority := 100) [Countable ι] [Infinite ι] : IsSiblingClosable ι :=
  ⟨fun S => by
    by_cases hS : S.Infinite
    · exact Or.inl (exists_injective_range_subset_of_infinite hS)
    · exact Or.inr (exists_injective_range_subset_of_infinite (Set.not_infinite.mp hS).infinite_compl)⟩

end IsSiblingClosable

/-- A finite set of slots leaves an infinite complement in a countable infinite
slot type, so the complement receives an injective copy of the slot type. -/
theorem exists_injective_notMem_of_finite {ι : Type*} [Countable ι] [Infinite ι] {S : Finset ι} :
    ∃ ψ : ι → ι, Function.Injective ψ ∧ ∀ i, ψ i ∉ (↑S : Set ι) := by
  obtain ⟨ψ, hψ, hsub⟩ := exists_injective_range_subset_of_infinite (S.finite_toSet.infinite_compl)
  exact ⟨ψ, hψ, fun i => by simpa using hsub ⟨i, rfl⟩⟩

end Branching

end Combinatorics

end
