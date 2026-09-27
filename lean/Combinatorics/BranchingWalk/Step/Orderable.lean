import Combinatorics.BranchingWalk.Step.Monotone

/-!
# The orderable form of a finitely supported step

A step with finitely many children can be relabelled into the thesis's normal form: list the children by
increasing mark, ties broken by the slot, and rename the `i`-th of them to `i`; every other slot is sent
outside the children, into the final segment the listing does not use. The listing is not built by
sorting a list — the rank of a child, the number of children strictly below it in the (mark, slot)
lexicographic order, is itself the label, so nothing here depends on a sorting API.

The entries below set up that rank, then build the listing as an increasing enumeration of the children of a
finitely supported step, and read orderability off that enumeration. The rank, and everything up to an
injection into the slots outside a finite set of children, is stated for an arbitrary slot type; only the
enumeration itself, whose length is the number of children, is about `ℕ`.
-/

namespace Combinatorics

namespace Branching

variable {ι X : Type*} [LinearOrder ι] [LinearOrder X]

/-- The children of a step on a finite set of slots that lie strictly below a given child, compared by
mark first and then by slot: those whose mark is smaller, or equal with a smaller slot. -/
noncomputable def Step.below (ξ : Step ι X) (S : Finset ι) (j : ι) : Finset ι := by
  classical
  exact S.filter fun j' => ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j))

theorem Step.mem_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} :
    j' ∈ ξ.below S j ↔
      j' ∈ S ∧ ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j)) := by
  classical
  exact Finset.mem_filter

/-- A child is not strictly below itself. -/
theorem Step.not_mem_below_self {ξ : Step ι X} {S : Finset ι} {j : ι} :
    j ∉ ξ.below S j := by
  classical
  intro h
  obtain ⟨-, x, y, hx, hy, hlt⟩ := Step.mem_below.mp h
  have hxy : x = y := Option.some.inj (by rw [hx] at hy; exact hy)
  rcases hlt with hlt' | ⟨heq, hjj⟩
  · exact absurd hxy (ne_of_lt hlt')
  · exact (lt_irrefl j) hjj

/-- The children strictly below one child are a subset of those strictly below a child that comes later in
the (mark, slot) order. -/
theorem Step.below_subset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι}
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    ξ.below S j ⊆ ξ.below S j' := by
  classical
  obtain ⟨xm, ym, hjm, hj'm, hlt⟩ := hrel
  intro a ha
  obtain ⟨haS, xa, xb, hax, hjx, halt⟩ := Step.mem_below.mp ha
  have hb : xb = xm := by
    rw [hjx] at hjm
    exact Option.some.inj hjm
  refine Step.mem_below.mpr ⟨haS, ?_⟩
  rcases halt with hlt' | ⟨heq, haj⟩
  · refine ⟨xa, ym, hax, hj'm, Or.inl ?_⟩
    rcases hlt with hlt'' | ⟨heq', -⟩
    · exact (hb ▸ hlt').trans hlt''
    · exact (hb.trans heq') ▸ hlt'
  · refine ⟨xa, ym, hax, hj'm, ?_⟩
    rcases hlt with hlt'' | ⟨heq', hjj'⟩
    · exact Or.inl ((heq.trans hb).symm ▸ hlt'')
    · exact Or.inr ⟨heq.trans (hb.trans heq'), haj.trans hjj'⟩

/-- The inclusion above is strict: the child itself lies on the right of it. -/
theorem Step.below_ssubset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} (hjS : j ∈ S)
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    ξ.below S j ⊂ ξ.below S j' := by
  classical
  refine ⟨Step.below_subset_of_below hrel, fun hsub => ?_⟩
  have hj' : j ∈ ξ.below S j' := Step.mem_below.mpr ⟨hjS, hrel⟩
  exact Step.not_mem_below_self (hsub hj')

/-- The rank of a slot among the children: the number of children strictly below it. -/
noncomputable def Step.rank (ξ : Step ι X) (S : Finset ι) (j : ι) : ℕ :=
  (ξ.below S j).card

/-- The rank separates the children of a finite set of slots: two of them with the same rank are the same
slot. The marks are comparable, so one of the two children is strictly below the other in the (mark, slot)
order, which makes its set of children below it a strict subset of the other's. -/
theorem Step.rank_injOn {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ) :
    Set.InjOn (ξ.rank S) ↑S := by
  classical
  intro j hjS j' hj'S h
  by_contra hne
  obtain ⟨x, hx⟩ := hS hjS
  obtain ⟨y, hy⟩ := hS hj'S
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Finset.card_lt_card
      (Step.below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inl hlt⟩)))
  · rcases lt_or_gt_of_ne hne with hjj | hjj
    · exact absurd h (ne_of_lt (Finset.card_lt_card
        (Step.below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inr ⟨heq, hjj⟩⟩)))
    · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
        (Step.below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inr ⟨heq.symm, hjj⟩⟩)))
  · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
      (Step.below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inl hgt⟩)))

/-- The rank of a child is smaller than the number of children: the children below it all lie in the
children with it removed. -/
theorem Step.rank_lt_card {ξ : Step ι X} {S : Finset ι} {j : ι} (hjS : j ∈ S) :
    ξ.rank S j < S.card := by
  classical
  have hsub : ξ.below S j ⊆ S.erase j := by
    intro a ha
    obtain ⟨haS, -⟩ := Step.mem_below.mp ha
    refine Finset.mem_erase.mpr ⟨?_, haS⟩
    intro haj
    exact Step.not_mem_below_self (haj ▸ ha)
  have hle : (ξ.below S j).card ≤ (S.erase j).card := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hjS] at hle
  exact lt_of_le_of_lt hle (Nat.sub_one_lt (Finset.card_ne_zero.mpr ⟨j, hjS⟩))

/-- On a finite set of children the rank takes exactly the values below the number of children, so every
label below that number is the rank of one child. -/
theorem Step.image_rank_eq_range {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ) :
    S.image (ξ.rank S) = Finset.range S.card := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (Step.rank_lt_card hjS)
  · rw [Finset.card_image_of_injOn (Step.rank_injOn hS), Finset.card_range]

/-- Children ordered by rank are ordered by mark: a child whose rank is no larger than another's cannot
carry the larger mark, since the children below it would then be strictly fewer. -/
theorem Step.exists_some_le_of_rank_le {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ)
    {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (h : ξ.rank S a ≤ ξ.rank S b) :
    ∃ x y, ξ a = some x ∧ ξ b = some y ∧ x ≤ y := by
  classical
  obtain ⟨x, hx⟩ := hS ha
  obtain ⟨y, hy⟩ := hS hb
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact ⟨x, y, hx, hy, le_of_lt hlt⟩
  · exact ⟨x, y, hx, hy, le_of_eq heq⟩
  · exact absurd h (not_le_of_gt (Finset.card_lt_card
      (Step.below_ssubset_of_below hb ⟨y, x, hy, hx, Or.inl hgt⟩)))

/-- A finite set of slots leaves an infinite complement in a countable infinite slot type, so an injection
into that complement exists — in particular the slots outside the children of a finitely supported step. -/
theorem exists_injective_notMem_of_finite {ι : Type*} [Countable ι] [Infinite ι] {S : Finset ι} :
    ∃ ψ : ι → ι, Function.Injective ψ ∧ ∀ i, ψ i ∉ (↑S : Set ι) := by
  classical
  have hcompl : ((↑S : Set ι)ᶜ).Infinite := by
    by_contra hc
    have hcfin : ((↑S : Set ι)ᶜ).Finite := Set.not_infinite.mp hc
    have hun : (Set.univ : Set ι).Finite :=
      ((S.finite_toSet).union hcfin).subset fun x _ => by simp
    exact Set.infinite_univ.not_finite hun
  let e : ℕ ↪ ↥((↑S : Set ι)ᶜ) := Set.Infinite.natEmbedding _ hcompl
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat ι
  exact ⟨fun i => (e (g i) : ι), fun a b hab => hg (e.injective (Subtype.coe_injective hab)),
    fun i => (e (g i)).2⟩

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
  have hmem : ∀ i, i < S.card → ∃ j ∈ S, ξ.rank S j = i := by
    intro i hi
    have him : i ∈ S.image (ξ.rank S) := by
      rw [Step.image_rank_eq_range hSsub]
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
  have hf_rank : ∀ i (hi : i < S.card), ξ.rank S (f i) = i := by
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
      · have hji : ξ.rank S (f i) = ξ.rank S (f j) := by rw [hij]
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
    have hlt : ξ.rank S j < S.card := Step.rank_lt_card hjS
    refine ⟨ξ.rank S j, hlt, ?_⟩
    rw [hf_lt (ξ.rank S j) hlt]
    exact Step.rank_injOn hSsub (hmem (ξ.rank S j) hlt).choose_spec.1 hjS
      (hmem (ξ.rank S j) hlt).choose_spec.2
  · intro i j hij hjn x y hx hy
    have hic : i < S.card := hij.trans hjn
    have hrank : ξ.rank S (f i) ≤ ξ.rank S (f j) := by
      rw [hf_rank i hic, hf_rank j hjn]
      exact le_of_lt hij
    obtain ⟨x', y', hx', hy', hle⟩ :=
      Step.exists_some_le_of_rank_le hSsub (hf_mem i hic) (hf_mem j hjn) hrank
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
