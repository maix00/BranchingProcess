/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite prefixes of ordered child slots

The ordered child slots used by finite-`N` selection need not literally be
`ℕ`. For a linear locally finite order with a least element and no greatest
element, `firstSlots α N` is the `Finset.Iio` initial interval cut off at rank
`N` through mathlib's order isomorphism with `ℕ`.

The public declarations in `Combinatorics.Branching` are:

- `slotOrderIsoNat`: the canonical order isomorphism
  $e:\alpha\simeq_o\mathbb N$, with assumptions
  `[LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]`.
- `firstSlots`: the finite initial interval
  $\operatorname{Finset.Iio}(e^{-1}(N))$, where `slotOrderIsoNat α` is the
  canonical order isomorphism $e:\alpha\simeq_o\mathbb N$.
- `mem_firstSlots_iff`:
  $i\in\texttt{firstSlots}(\alpha,N)\leftrightarrow e(i)<N$.
- `firstSlots_mono` and `card_firstSlots`:
  $M\le N\Rightarrow\texttt{firstSlots}(\alpha,M)\subseteq
  \texttt{firstSlots}(\alpha,N)$ and
  $|\texttt{firstSlots}(\alpha,N)|=N$.
- `lt_of_mem_firstSlots_of_not_mem`: every member of the first $N$ slots
  precedes every slot outside that prefix.
- `exists_mem_firstSlots`: every slot belongs to some finite prefix.
- `iUnion_firstSlots`: $\bigcup_N\texttt{firstSlots}(\alpha,N)=\alpha$.
- `exists_subset_firstSlots`: every finite subset of $\alpha$ is contained
  in one first-$N$ prefix.
-/

@[expose] public section

namespace Combinatorics.Branching

open scoped BigOperators

/-- The mathlib-derived order isomorphism from an abstract slot order to
`ℕ`, used as the canonical rank map for child slots. -/
noncomputable def slotOrderIsoNat (α : Type*) [LinearOrder α]
    [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α] : α ≃o ℕ := by
  letI := LinearLocallyFiniteOrder.succOrder α
  letI := LinearLocallyFiniteOrder.predOrder α
  exact orderIsoNatOfLinearSuccPredArch

/-- The finite set of the first `N` slots in an abstract order of type
`ℕ`, represented by mathlib's finite strict initial interval. -/
noncomputable def firstSlots (α : Type*) [LinearOrder α]
    [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (N : ℕ) : Finset α :=
  Finset.Iio ((slotOrderIsoNat α).symm N)

theorem mem_firstSlots_iff
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] {i : α} {N : ℕ} :
    i ∈ firstSlots α N ↔ slotOrderIsoNat α i < N := by
  let e := slotOrderIsoNat α
  rw [firstSlots, Finset.mem_Iio]
  have h := e.lt_iff_lt (x := i) (y := e.symm N)
  simpa using h.symm

theorem firstSlots_mono
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] {M N : ℕ} (hMN : M ≤ N) :
    firstSlots α M ⊆ firstSlots α N := by
  intro i hi
  rw [mem_firstSlots_iff] at hi ⊢
  exact lt_of_lt_of_le hi hMN

@[simp] theorem card_firstSlots
    (α : Type*) [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (N : ℕ) :
    (firstSlots α N).card = N := by
  let e := slotOrderIsoNat α
  have hmap : (firstSlots α N).map e.toEmbedding = Finset.range N := by
    ext n
    simp [firstSlots, e]
  calc
    (firstSlots α N).card = ((firstSlots α N).map e.toEmbedding).card := by simp
    _ = (Finset.range N).card := by rw [hmap]
    _ = N := Finset.card_range N

/-- Every member of the first `N` slots precedes every slot outside that
prefix. -/
theorem lt_of_mem_firstSlots_of_not_mem
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] {N : ℕ} {i j : α}
    (hi : i ∈ firstSlots α N) (hj : j ∉ firstSlots α N) :
    i < j := by
  rw [mem_firstSlots_iff] at hi
  rw [mem_firstSlots_iff, not_lt] at hj
  exact (slotOrderIsoNat α).lt_iff_lt.mp (lt_of_lt_of_le hi hj)

/-- Every slot belongs to a sufficiently long finite prefix. -/
theorem exists_mem_firstSlots
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (i : α) :
    ∃ N : ℕ, i ∈ firstSlots α N := by
  refine ⟨slotOrderIsoNat α i + 1, ?_⟩
  rw [mem_firstSlots_iff]
  exact Nat.lt_succ_self _

/-- The increasing finite prefixes exhaust all ordered slots. -/
theorem iUnion_firstSlots
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] :
    (⋃ N : ℕ, (firstSlots α N : Set α)) = Set.univ := by
  ext i
  simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_univ, iff_true]
  exact exists_mem_firstSlots i

/-- Every finite collection of slots is contained in one initial prefix. -/
theorem exists_subset_firstSlots
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (s : Finset α) :
    ∃ N : ℕ, s ⊆ firstSlots α N := by
  classical
  refine ⟨∑ i ∈ s, (slotOrderIsoNat α i + 1), ?_⟩
  intro i hi
  rw [mem_firstSlots_iff]
  have hle : slotOrderIsoNat α i + 1 ≤
      ∑ j ∈ s, (slotOrderIsoNat α j + 1) := by
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (slotOrderIsoNat α j + 1)) hi
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hle


end Combinatorics.Branching

end
