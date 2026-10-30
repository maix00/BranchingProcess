/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Ordering.Monotone
import all Combinatorics.BranchingWalk.Step.Ordering.Lemmas.FiniteRank

/-!
# The orderable form of a finitely supported step

## Public declarations

`Step.IsOrderable` is the property that an injective relabelling of the slots, covering every surviving
slot, makes a step sibling closed and increasing: a normal form listing all children from the left by
increasing displacement.
This file owns the orderability predicate, the chosen increasing normal form,
and the theorem that finitely supported steps on $\mathbb N$ admit such a
normal form. The finite mark-slot rank used in the construction is an internal
proof component in `Step/Ordering/Lemmas/FiniteRank.lean`; the rank is not part
of this module's public interface.

The public declarations in `Combinatorics.Branching` are:

- `Step.IsOrderable ξ`: there is an injective relabelling $f$ such that
  $i\mapsto\xi(f(i))$ is sibling-closed and increasing, and every surviving
  slot of $\xi$ lies in the range of $f$.
- `Step.orderingRelabel ξ h` and `Step.order ξ h`: the chosen relabelling and
  the resulting increasing normal form; `Step.orderingRelabel_injective`,
  `Step.order_mem_orderedSteps`, and
  `Step.orderingRelabel_surjectiveOn_support` give injectivity, normal-form
  membership, and coverage of surviving slots.
- `Step.leftmost? ξ h`: the value at the least slot of the normal form;
  `Step.leftmost?_eq_some_le` says that when $\xi$ has a child, this value is
  present and is at most every raw child displacement.
- `Step.isOrderable_of_isSiblingClosed_of_isMonotone`: an already
  sibling-closed, increasing step is orderable by the identity relabelling.
- `IsOrderable ι X`: every step $\xi: \operatorname{Step}(\iota,X)$ is
  `Step.IsOrderable ξ`.
- `Step.HasIncreasingEnumeration ξ`: there are a length $n$ and an injection
  $e$ whose image is exactly the surviving slots, with $e(i)$ surviving for
  $i<n$, and whose marks are nondecreasing for indices below $n$.
  `Step.isOrderable_of_hasIncreasingEnumeration` converts such an
  enumeration to an orderability witness.
- `Step.hasIncreasingEnumeration_of_isFinitelySupported` and
  `Step.isOrderable_of_isFinitelySupported`: every finitely supported step
  on $\mathbb N$ has an increasing enumeration and is orderable.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- An infinite subset of a countably infinite type contains an injective
copy of the whole type. -/
private lemma exists_injective_range_subset_of_infinite
    {ι : Type*} [Countable ι] {T : Set ι} (hT : T.Infinite) :
    ∃ f : ι → ι, Function.Injective f ∧ Set.range f ⊆ T := by
  obtain ⟨g, hg⟩ := (exists_injective_nat ι : ∃ g : ι → ℕ, Function.Injective g)
  let e : ℕ ↪ ↥T := hT.natEmbedding
  exact ⟨fun i => (e (g i) : ι),
    fun i j hij => hg (e.injective (Subtype.coe_injective hij)),
    by rintro _ ⟨i, rfl⟩; exact (e (g i)).2⟩

/-- An infinite countable slot type can be injectively relabeled outside any
finite set of forbidden slots. -/
private lemma exists_injective_notMem_of_finite
    {ι : Type*} [Countable ι] [Infinite ι] {S : Finset ι} :
    ∃ ψ : ι → ι, Function.Injective ψ ∧ ∀ i, ψ i ∉ (↑S : Set ι) := by
  obtain ⟨ψ, hψ, hsub⟩ :=
    exists_injective_range_subset_of_infinite (S.finite_toSet.infinite_compl)
  exact ⟨ψ, hψ, fun i => by simpa using hsub ⟨i, rfl⟩⟩

section IsOrderable

variable {ι X : Type*} [LT ι] [LE X]

/-- A step is orderable when an injective relabeling covering every surviving
slot makes it both sibling closed and increasing. Thus the surviving slots
become an initial segment containing every original child, and their marks
increase along the slot order. The direction of the mark comparison is the
one of `X`, so the mirrored form is read in `OrderDual X`. -/
class Step.IsOrderable (ξ : Step ι X) : Prop where
  exists_relabel : ∃ f : ι → ι, Function.Injective f ∧
    Step.IsSiblingClosed (fun i => ξ (f i)) ∧
    IsMonotone (fun i => ξ (f i)) ∧
    ∀ j, survive ξ j → ∃ i, f i = j

/-- A chosen relabelling that puts an orderable step into increasing sibling
order.  The proof of orderability remains a property; no wrapper type is
introduced for the result. -/
noncomputable def Step.orderingRelabel (ξ : Step ι X)
    (h : ξ.IsOrderable) : ι → ι :=
  Classical.choose h.exists_relabel

theorem Step.orderingRelabel_injective (ξ : Step ι X)
    (h : ξ.IsOrderable) : Function.Injective (ξ.orderingRelabel h) :=
  (Classical.choose_spec h.exists_relabel).1

/-- Reindex an orderable step into its chosen increasing normal form. -/
noncomputable def Step.order (ξ : Step ι X)
    (h : ξ.IsOrderable) : Step ι X :=
  fun i => ξ (ξ.orderingRelabel h i)

theorem Step.order_mem_orderedSteps (ξ : Step ι X)
    (h : ξ.IsOrderable) : ξ.order h ∈ orderedSteps :=
  ⟨(Classical.choose_spec h.exists_relabel).2.1,
    (Classical.choose_spec h.exists_relabel).2.2.1⟩

/-- The chosen ordered normal form contains every child of the raw step. -/
theorem Step.orderingRelabel_surjectiveOn_support (ξ : Step ι X)
    (h : ξ.IsOrderable) {j : ι} (hj : survive ξ j) :
    ∃ i, ξ.orderingRelabel h i = j :=
  (Classical.choose_spec h.exists_relabel).2.2.2 j hj

section FirstOrderedChild

variable {ι X : Type*} [PartialOrder ι] [OrderBot ι] [LinearOrder X]

/-- The first displacement after ordering an orderable step. It is read at the
least slot and is partial because a branching step may have no children. -/
noncomputable def Step.leftmost? (ξ : Step ι X)
    (h : ξ.IsOrderable) : Option X :=
  ξ.order h ⊥

/-- If the raw step has a child, `leftmost?` is present and is no larger than
the displacement of every raw child.  Coverage in `IsOrderable` is essential:
without it a relabelling could silently omit the true leftmost child. -/
theorem Step.leftmost?_eq_some_le (ξ : Step ι X)
    (h : ξ.IsOrderable) (hne : ∃ j, survive ξ j) :
    ∃ x, ξ.leftmost? h = some x ∧
      ∀ j y, ξ j = some y → x ≤ y := by
  obtain ⟨j, hj⟩ := hne
  obtain ⟨i, hi⟩ := ξ.orderingRelabel_surjectiveOn_support h hj
  have hiSurvive : survive (ξ.order h) i := by
    change survive ξ (ξ.orderingRelabel h i)
    rw [hi]
    exact hj
  have hordered := ξ.order_mem_orderedSteps h
  have hfirst : survive (ξ.order h) ⊥ :=
    orderedSteps_survive_of_le (ξ.order h) hordered bot_le hiSurvive
  obtain ⟨x, hx⟩ := hfirst
  refine ⟨x, hx, ?_⟩
  intro k y hky
  obtain ⟨r, hr⟩ := ξ.orderingRelabel_surjectiveOn_support h ⟨y, hky⟩
  have hry : ξ.order h r = some y := by simp [Step.order, hr, hky]
  by_cases hr0 : r = ⊥
  · subst r
    exact le_of_eq (Option.some.inj (hx.symm.trans hry))
  · exact hordered.2 ⊥ r x y (bot_lt_iff_ne_bot.mpr hr0) hx hry

end FirstOrderedChild

/-- A step that is already sibling closed and increasing is orderable: the identity relabels nothing. -/
theorem Step.isOrderable_of_isSiblingClosed_of_isMonotone {ξ : Step ι X}
    (hclosed : Step.IsSiblingClosed ξ) (hmono : IsMonotone ξ) : Step.IsOrderable ξ :=
  ⟨id, Function.injective_id, hclosed, hmono, fun j _ => ⟨j, rfl⟩⟩

/-- On a pair of a slot type and a mark type, every step is orderable. This is the strong form of the
property, and it is a property of the pair rather than of a step: it fails for a mark type in which a
family of children has no leftmost member, whatever the slot type. Finiteness of the support is a
sufficient condition and not the definition — `Step.IsFinitelySupported` states it — and a step with
infinitely many children is orderable as soon as those children can be listed from the left with
nondecreasing marks. -/
def IsOrderable (ι X : Type*) [LT ι] [LE X] : Prop :=
  ∀ ξ : Step ι X, Step.IsOrderable ξ

/-- A step has an increasing enumeration of its children when they can be listed in one go, without gaps
and with marks that do not decrease: a slot `n` and an injection `e` whose range is exactly the children,
its domain the initial segment below `n`, along which an earlier member of the listing never carries a
larger mark. Finiteness is not asked — an infinite family of children has one as soon as it can be counted
from the left with nondecreasing marks, and such a step is orderable by
`Step.isOrderable_of_hasIncreasingEnumeration`. The domain is an initial
segment: `Step.IsSiblingClosed` says that an absent slot forces every larger one absent, so the surviving
slots are the initial segment and the children of a closed step are the leftmost slots. -/
def Step.HasIncreasingEnumeration (ξ : Step ι X) : Prop :=
  ∃ n : ι, ∃ e : ι → ι, Function.Injective e ∧ (∀ i, i < n → survive ξ (e i)) ∧
    (∀ j, survive ξ j → ∃ i, i < n ∧ e i = j) ∧
    ∀ i j, i < j → j < n → ∀ x y, ξ (e i) = some x → ξ (e j) = some y → x ≤ y

end IsOrderable

section IsOrderableOfEnumeration

variable {ι X : Type*} [Preorder ι] [LE X]

/-- A step that has an increasing enumeration of its children is orderable, and the enumeration itself is the
relabelling. Its surviving slots are exactly the initial segment below the length of the listing: a slot of
the relabelled step survives when the listing sends it to a surviving slot, the listing sends the slots below
that length to surviving slots, and conversely every surviving slot is named by the listing below that length,
so injectivity puts the name below that length as well. The marks grow along that initial segment, which is
the listing's own clause, and a later survivor forces every earlier slot to survive because an initial segment
is closed downwards. Nothing here needs the slot type to be countable, and nothing is sent outside the
children: the listing already is an injective relabelling. -/
theorem Step.isOrderable_of_hasIncreasingEnumeration {ξ : Step ι X}
    (h : ξ.HasIncreasingEnumeration) : ξ.IsOrderable := by
  classical
  obtain ⟨n, e, hinj, hls, hsurj, hmono⟩ := h
  have hiff : ∀ i, survive (fun i => ξ (e i)) i ↔ i < n := by
    intro i
    refine ⟨?_, hls i⟩
    intro hs
    obtain ⟨i', hi'n, hi'eq⟩ := hsurj (e i) hs
    rwa [hinj hi'eq] at hi'n
  refine ⟨e, hinj, ?_, ?_, ?_⟩
  · intro i j hij hi
    by_contra hj
    have hjn : j < n := (hiff j).mp ((survive_iff_ne_none _ j).mpr hj)
    exact ((survive_iff_ne_none _ i).mp ((hiff i).mpr (hij.trans hjn))) hi
  · intro i j x y hij hx hy
    exact hmono i j hij ((hiff j).mp ⟨y, hy⟩) x y hx hy
  · intro j hj
    obtain ⟨i, _, hi⟩ := hsurj j hj
    exact ⟨i, hi⟩

end IsOrderableOfEnumeration

section Nat

variable {X : Type*} [LinearOrder X]

/-- A finitely supported step on `ℕ` has an increasing enumeration of its children: label each child by
its rank, so that the children occupy exactly the labels below their number, and name every other label by a
slot outside the children, whose complement is infinite. Along those labels the marks do not decrease,
children ordered by rank being ordered by mark.

The slot type is `ℕ` here, and only here: the enumeration of `Step.HasIncreasingEnumeration` is indexed by an
initial segment whose length is the number of children, so the slots below that length have to be exactly as
many as there are children, which is what the slots below `S.card` are. Where there are infinitely many
slots below every `n`, as in `ℤ`, no such enumeration exists for a finitely supported step: the listing sends
every slot below `n` to a survivor, so there would be infinitely many children. -/
theorem Step.hasIncreasingEnumeration_of_isFinitelySupported {ξ : Step ℕ X}
    (h : ξ.IsFinitelySupported) : ξ.HasIncreasingEnumeration := by
  classical
  obtain ⟨hfin⟩ := h
  set S : Finset ℕ := hfin.toFinset with hSdef
  have hScoe : (↑S : Set ℕ) = support ξ := by
    rw [hSdef]
    exact hfin.coe_toFinset
  have hSsub : ↑S ⊆ support ξ := fun _ hx => hScoe ▸ hx
  obtain ⟨ψ, hψinj, hψnot⟩ := exists_injective_notMem_of_finite (S := S)
  have hmem : ∀ i, i < S.card → ∃ j ∈ S, Step.Ordering.Lemmas.rank ξ S j = i := by
    intro i hi
    have him : i ∈ S.image (Step.Ordering.Lemmas.rank ξ S) := by
      rw [Step.Ordering.Lemmas.image_rank_eq_range hSsub]
      exact Finset.mem_range.mpr hi
    obtain ⟨j, hjS, hji⟩ := Finset.mem_image.mp him
    exact ⟨j, hjS, hji⟩
  let f : ℕ → ℕ := fun i => if hi : i < S.card then (hmem i hi).choose else ψ (i - S.card)
  have hf_lt : ∀ i (hi : i < S.card), f i = (hmem i hi).choose := by
    intro i hi
    simp only [f, dite_eq_left hi]
  have hf_ge : ∀ i, ¬ i < S.card → f i = ψ (i - S.card) := by
    intro i hi
    simp only [f, dite_eq_right hi]
  have hf_mem : ∀ i (hi : i < S.card), f i ∈ S := by
    intro i hi
    rw [hf_lt i hi]
    exact (hmem i hi).choose_spec.1
  have hf_rank : ∀ i (hi : i < S.card), Step.Ordering.Lemmas.rank ξ S (f i) = i := by
    intro i hi
    rw [hf_lt i hi]
    exact (hmem i hi).choose_spec.2
  have hf_notmem : ∀ i, ¬ i < S.card → f i ∉ (↑S : Set ℕ) := by
    intro i hi
    rw [hf_ge i hi]
    exact hψnot _
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_cases hi : i < S.card
    · by_cases hj : j < S.card
      · have hji : Step.Ordering.Lemmas.rank ξ S (f i) = Step.Ordering.Lemmas.rank ξ S (f j) := by rw [hij]
        rw [hf_rank i hi, hf_rank j hj] at hji
        exact hji
      · exact absurd (hij ▸ hf_mem i hi) (hf_notmem j hj)
    · by_cases hj : j < S.card
      · exact absurd (hij.symm ▸ hf_mem j hj) (hf_notmem i hi)
      · have hsub : i - S.card = j - S.card := hψinj (by rw [← hf_ge i hi, ← hf_ge j hj, hij])
        have hiK : S.card ≤ i := Nat.le_of_not_lt hi
        have hjK : S.card ≤ j := Nat.le_of_not_lt hj
        omega
  refine ⟨S.card, f, hf_inj, ?_, ?_, ?_⟩
  · intro i hi
    exact hSsub (Finset.mem_coe.mpr (hf_mem i hi))
  · intro j hj
    have hjS : j ∈ S := by
      have hjs : j ∈ (↑S : Set ℕ) := by
        rw [hScoe]
        exact hj
      exact Finset.mem_coe.mp hjs
    have hlt : Step.Ordering.Lemmas.rank ξ S j < S.card := Step.Ordering.Lemmas.rank_lt_card hjS
    refine ⟨Step.Ordering.Lemmas.rank ξ S j, hlt, ?_⟩
    rw [hf_lt (Step.Ordering.Lemmas.rank ξ S j) hlt]
    exact Step.Ordering.Lemmas.rank_injOn hSsub (hmem (Step.Ordering.Lemmas.rank ξ S j) hlt).choose_spec.1 hjS
      (hmem (Step.Ordering.Lemmas.rank ξ S j) hlt).choose_spec.2
  · intro i j hij hjn x y hx hy
    have hic : i < S.card := hij.trans hjn
    have hrank : Step.Ordering.Lemmas.rank ξ S (f i) ≤ Step.Ordering.Lemmas.rank ξ S (f j) := by
      rw [hf_rank i hic, hf_rank j hjn]
      exact le_of_lt hij
    obtain ⟨x', y', hx', hy', hle⟩ :=
      Step.Ordering.Lemmas.exists_some_le_of_rank_le hSsub (hf_mem i hic) (hf_mem j hjn) hrank
    have hxx : x = x' := Option.some.inj (hx.symm.trans hx')
    have hyy : y = y' := Option.some.inj (hy.symm.trans hy')
    simpa [hxx, hyy] using hle

/-- A finitely supported step on `ℕ` is orderable, by the general theorem: the enumeration above is the
relabelling. -/
theorem Step.isOrderable_of_isFinitelySupported {ξ : Step ℕ X} (h : ξ.IsFinitelySupported) :
    ξ.IsOrderable :=
  Step.isOrderable_of_hasIncreasingEnumeration (Step.hasIncreasingEnumeration_of_isFinitelySupported h)
end Nat

end Branching

end Combinatorics

end
