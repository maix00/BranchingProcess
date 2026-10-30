/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/

module

import MeasureTheory.Analytic.Paving.Basic

/-!
# Finite-union representations used in paving proofs

This module contains proof-level conversions used by the projection arguments.
It is an internal `Lemmas` module rather than part of the public paving API.

## Internal proof declarations

- `mem_supClosure_set_iff_natIndexedUnion` rewrites
  $s\in\operatorname{supClosure}(S)$ as a union over a nonempty finite set of natural
  indices: there are $t\subseteq_{\mathrm{fin}}\mathbb N$ and
  $A:\mathbb N\to\mathrm{Set}(\alpha)$ such that $A_n\in S$ for $n\in t$
  and $s=\bigcup_{n\in t}A_n$.
-/

open Set

namespace MeasureTheory.Analytic.Paving

variable {α : Type*} {S : Set (Set α)}

/-- Express finite-sup-closure membership using a finite family indexed by `ℕ`.

This representation is used by the projection proofs that enumerate a finite
union and keep track of its individual members. -/
lemma mem_supClosure_set_iff_natIndexedUnion (s : Set α) :
    s ∈ supClosure S ↔ ∃ (t : Finset ℕ) (_ : t.Nonempty) (A : ℕ → Set α),
      (∀ n ∈ t, A n ∈ S) ∧ s = ⋃ n ∈ t, A n := by
  rw [MeasureTheory.Analytic.mem_supClosure_set_iff]
  refine ⟨fun ⟨L, hL_nonempty, hL_eq, hL_subset⟩ ↦ ?_, fun ⟨t, ht_nonempty, A, hA, h_eq⟩ ↦ ?_⟩
  · classical
    have hcard : L.toList.length = L.card := Finset.length_toList L
    refine ⟨Finset.range L.card,
      Finset.nonempty_range_iff.mpr (Finset.card_ne_zero.mpr hL_nonempty),
      fun n ↦ if h : n < L.toList.length then L.toList[n] else ∅, ?_, ?_⟩
    · intro n hn
      rw [Finset.mem_range, ← hcard] at hn
      simp only [dite_eq_left hn]
      exact hL_subset (Finset.mem_coe.mpr (Finset.mem_toList.mp (List.getElem_mem hn)))
    · ext x
      rw [hL_eq]
      simp only [Set.mem_sUnion, Finset.mem_coe, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨u, hu, hxu⟩
        obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hu)
        exact ⟨n, hcard ▸ hn, by simpa only [dite_eq_left hn]⟩
      · rintro ⟨n, hn, hxn⟩
        rw [← hcard] at hn
        rw [dite_eq_left hn] at hxn
        exact ⟨_, Finset.mem_toList.mp (List.getElem_mem hn), hxn⟩
  · exact ⟨t.image A, by simpa, by simpa, by simpa⟩

end MeasureTheory.Analytic.Paving
