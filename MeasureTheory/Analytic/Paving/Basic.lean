/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import Mathlib.Order.CountableSupClosed
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Compactness.CompactSystem

/-!
# Finite closure operations and product pavings

This module develops finite-union and finite-intersection closure
characterizations and the product `σδ`-construction used in analytic
projections. Generic compact-system constructions are owned by
`Topology/Compactness/CompactSystem/Operations.lean`.

## Public declarations

The product `σδ`-paving consists of countable intersections of countable
unions of generating rectangles:

\[
s\in\operatorname{prodSigmaDelta}(p,q)
\iff \exists A,K,\quad
s=\bigcap_{n\in\mathbb N}\bigcup_{m\in\mathbb N}
A_{nm}\times K_{nm},\quad A_{nm}\in p,\ K_{nm}\in q.
\]

- `mem_supClosure_set_iff` and `mem_infClosure_set_iff`: membership in a
  finite-union or finite-intersection closure is equivalent to being a
  nonempty finite union or intersection of members of the original family.
- `mem_supClosure_insert_empty_iff` and `mem_infClosure_insert_univ_iff`:
  the same characterizations when the empty set or universal set is included
  in the generating family, with the nonemptiness condition omitted.
- `Paving.mem_image2_prod_mono`: `p ⊆ p'`, `q ⊆ q'`, and
  `s ∈ Set.image2 (· ×ˢ ·) p q` imply `s ∈ Set.image2 (· ×ˢ ·) p' q'`.
  `Paving.InfClosed.image2_prod` asserts that the product family is
  inf-closed when both factor families are inf-closed.
- `Paving.prodSigmaDelta p q` is
  `countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))`.
  `Paving.mem_prodSigmaDelta_iff` states that `s ∈ prodSigmaDelta p q` iff
  there are `A : ℕ → ℕ → Set 𝓧` and `K : ℕ → ℕ → Set 𝓚` such that
  `A n m ∈ p`, `K n m ∈ q`, and `s = ⋂ n, ⋃ m, A n m ×ˢ K n m`.
  The theorem
  `Paving.mem_countableSupClosure_image2_prod_iff` gives the analogous
  representation with `A : ℕ → Set 𝓧`, `K : ℕ → Set 𝓚`, `A n ∈ p`,
  `K n ∈ q`, and `s = ⋃ n, A n ×ˢ K n`.
- `Paving.mem_prodSigmaDelta_of_mem` embeds each rectangle `s ×ˢ t` with
  `s ∈ p` and `t ∈ q`; `Paving.prodSigmaDelta.mono` preserves membership when
  either generating family is enlarged.
- `InfClosed.mem_countableInfClosure_iff` and
  `SupClosed.mem_countableSupClosure_iff`: elements of the respective
  countable closures are countable intersections of antitone sequences and
  countable unions of monotone sequences.
-/

@[expose] public section

open Set

namespace MeasureTheory.Analytic

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)} {s t : Set 𝓧} {f : ℕ → Set 𝓧}

section Aux

variable {α : Type*} {S : Set (Set α)}

lemma mem_supClosure_set_iff (s : Set α) :
    s ∈ supClosure S ↔ ∃ L : Finset (Set α), L.Nonempty ∧ s = ⋃₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · choose hL_nonempty hL_subset hL_sup using hL
    refine ⟨L, hL_nonempty, ?_, hL_subset⟩
    rw [← hL_sup, ← Finset.sup_id_set_eq_sUnion, Finset.sup'_eq_sup]
  · obtain ⟨L, hL_nonempty, hL_eq, hL_subset⟩ := h
    refine ⟨L, hL_nonempty, hL_subset, ?_⟩
    rw [hL_eq, ← Finset.sup_id_set_eq_sUnion, Finset.sup'_eq_sup]

lemma mem_infClosure_set_iff (s : Set α) :
    s ∈ infClosure S ↔ ∃ L : Finset (Set α), L.Nonempty ∧ s = ⋂₀ L ∧ ↑L ⊆ S := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun h ↦ ?_⟩
  · choose hL_nonempty hL_subset hL_sup using hL
    refine ⟨L, hL_nonempty, ?_, hL_subset⟩
    rw [← hL_sup, ← Finset.inf_id_set_eq_sInter, Finset.inf'_eq_inf]
  · obtain ⟨L, hL_nonempty, hL_eq, hL_subset⟩ := h
    refine ⟨L, hL_nonempty, hL_subset, ?_⟩
    rw [hL_eq, ← Finset.inf_id_set_eq_sInter, Finset.inf'_eq_inf]


lemma mem_supClosure_insert_empty_iff (s : Set α) :
    s ∈ supClosure (insert ∅ S) ↔ ∃ L : Finset (Set α), s = ⋃₀ L ∧ ↑L ⊆ insert ∅ S := by
  rw [mem_supClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ⟨L, hL_eq, hL_subset⟩,
    fun ⟨L, hL_eq, hL_subset⟩ ↦ ?_⟩
  classical
  refine ⟨if L.Nonempty then L else {∅}, ?_, ?_, fun _ ↦ by simp; grind⟩
  · split_ifs
    · simpa
    · simp
  · rcases Finset.eq_empty_or_nonempty L with (rfl | hL_nonempty)
    · simpa using hL_eq
    · simpa [hL_nonempty]

lemma mem_infClosure_insert_univ_iff (s : Set α) :
    s ∈ infClosure (insert Set.univ S) ↔
      ∃ L : Finset (Set α), s = ⋂₀ L ∧ ↑L ⊆ insert Set.univ S := by
  rw [mem_infClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ⟨L, hL_eq, hL_subset⟩,
    fun ⟨L, hL_eq, hL_subset⟩ ↦ ?_⟩
  refine ⟨if L.Nonempty then L else {Set.univ}, ?_, ?_, fun _ ↦ by simp; grind⟩
  · split_ifs
    · simpa
    · simp
  · rcases Finset.eq_empty_or_nonempty L with rfl | hL_nonempty
    · simpa using hL_eq
    · simpa [hL_nonempty]

end Aux
namespace Paving

lemma mem_image2_prod_mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') {q' : Set (Set 𝓚)}
    (hq : q ⊆ q') {s : Set (𝓧 × 𝓚)} (hs : s ∈ Set.image2 (· ×ˢ ·) p q) :
    s ∈ Set.image2 (· ×ˢ ·) p' q' := by
  simp only [Set.mem_image2] at hs
  obtain ⟨A, hpA, B, hqB, rfl⟩ := hs
  exact ⟨A, hp (hpA), B, hq (hqB), rfl⟩

lemma InfClosed.image2_prod (hp_inter : InfClosed p) (hq_inter : InfClosed q) :
    InfClosed (Set.image2 (· ×ˢ ·) p q) := by
  intro A hA B hB
  obtain ⟨u, hu, v, hv, h_eq⟩ := hA
  obtain ⟨s, hs, t, ht, h_eq'⟩ := hB
  simp only [← h_eq, ← h_eq']
  exact ⟨u ∩ s, hp_inter hu hs, v ∩ t, hq_inter hv ht, by simp; grind⟩

/-- The set is a countable intersection of countable unions of sets that can be written as a
product of two sets, each satisfying a property. -/
def prodSigmaDelta (p : Set (Set 𝓧)) (q : Set (Set 𝓚)) : Set (Set (𝓧 × 𝓚)) :=
  countableInfClosure (countableSupClosure (Set.image2 (· ×ˢ ·) p q))


lemma mem_prodSigmaDelta_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ prodSigmaDelta p q ↔
      ∃ (A : ℕ → ℕ → Set 𝓧) (_ : ∀ n m, A n m ∈ p) (K : ℕ → ℕ → Set 𝓚) (_ : ∀ n m, K n m ∈ q),
        s = ⋂ n, ⋃ m, A n m ×ˢ K n m := by
  unfold prodSigmaDelta
  simp only [mem_countableInfClosure_iff_iInf, mem_countableSupClosure_iff_iSup, Set.mem_image2,
    Set.iSup_eq_iUnion, Set.iInf_eq_iInter, exists_prop]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB hB' using hA
    choose C hC hC' using hB
    choose D hD hD' using hC'
    refine ⟨C, hC, D, hD, ?_⟩
    rw [← hs]
    simp_rw [hD', ← hB']
  · obtain ⟨A, hA, K, hK, rfl⟩ := h
    refine ⟨fun n ↦ ⋃ m, A n m ×ˢ K n m, fun n ↦ ⟨fun m ↦ A n m ×ˢ K n m, fun m ↦ ?_, rfl⟩, rfl⟩
    exact ⟨A n m, hA n m, ⟨K n m, hK n m, rfl⟩⟩

lemma mem_countableSupClosure_image2_prod_iff {s : Set (𝓧 × 𝓚)} :
    s ∈ countableSupClosure (Set.image2 (· ×ˢ ·) p q) ↔
      ∃ (A : ℕ → Set 𝓧) (_ : ∀ n, A n ∈ p) (K : ℕ → Set 𝓚) (_ : ∀ n, K n ∈ q),
        s = ⋃ n, A n ×ˢ K n := by
  simp only [mem_countableSupClosure_iff_iSup, Set.mem_image2]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · choose A hA hs using h
    choose B hB C hC hA_eq using hA
    refine ⟨B, hB, C, hC, ?_⟩
    simp_rw [← hs, hA_eq]
    rfl
  · obtain ⟨A, hA, K, hK, rfl⟩ := h
    exact ⟨fun n ↦ A n ×ˢ K n, fun n ↦ ⟨A n, hA n, K n, hK n, rfl⟩, rfl⟩

lemma mem_prodSigmaDelta_of_mem {s : Set 𝓧} {t : Set 𝓚} (hs : s ∈ p) (hq : t ∈ q) :
    s ×ˢ t ∈ prodSigmaDelta p q := by
  rw [mem_prodSigmaDelta_iff]
  exact ⟨fun n m ↦ s, fun _ _ ↦ hs, fun n m ↦ t, fun _ _ ↦ hq, by
    simp [Set.iInter_const, Set.iUnion_const]⟩

lemma prodSigmaDelta.mono {p' : Set (Set 𝓧)} {q' : Set (Set 𝓚)} (hp : p ⊆ p') (hq : q ⊆ q')
    {s : Set (𝓧 × 𝓚)} (hs : s ∈ prodSigmaDelta p q) :
    s ∈ prodSigmaDelta p' q' := by
  simp_rw [mem_prodSigmaDelta_iff] at hs ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs
  exact ⟨A, fun n m ↦ hp (hA n m), K, fun n m ↦ hq (hK n m), rfl⟩

/-- If the set is inf-closed, elements of `countablInfClosure` can be written as countable
intersections of *antitone* sequences of sets. -/
lemma InfClosed.mem_countableInfClosure_iff (hp : InfClosed p) {s : Set 𝓧} :
    s ∈ countableInfClosure p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Antitone A ∧ s = ⋂ n, A n := by
  rw [mem_countableInfClosure_iff_iInf]
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, _, h_eq⟩ ↦ ⟨A, hA, h_eq.symm⟩⟩
  choose A hA hs using h
  refine ⟨Set.dissipate A, fun n ↦ ?_, Set.antitone_dissipate, ?_⟩
  · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp hn (hA _)
  · rw [Set.iInter_dissipate, ← hs]
    rfl

/-- If the set is sup-closed, elements of `countableSupClosure` can be written as countable
unions of *monotone* sequences of sets. -/
protected
lemma SupClosed.mem_countableSupClosure_iff (hp : SupClosed p) {s : Set 𝓧} :
    s ∈ countableSupClosure p ↔ ∃ A : ℕ → Set 𝓧, (∀ n, A n ∈ p) ∧ Monotone A ∧ s = ⋃ n, A n := by
  rw [mem_countableSupClosure_iff_iSup]
  simp only [Set.iSup_eq_iUnion]
  refine ⟨fun h ↦ ?_, fun ⟨A, hA, _, h_eq⟩ ↦ ⟨A, hA, h_eq.symm⟩⟩
  choose A hA hs using h
  refine ⟨Set.accumulate A, fun n ↦ ?_, Set.monotone_accumulate, ?_⟩
  · induction n with
    | zero => simp [hA]
    | succ n hn =>
      rw [Set.accumulate_succ]
      exact hp hn (hA _)
  · rw [Set.iUnion_accumulate, ← hs]


end Paving
end MeasureTheory.Analytic

end
