/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Finite
public import Combinatorics.BranchingWalk.Step.Count
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Selecting the first slots of a branching step

In a locally finite linear order with a least slot, every step admits a first
`N`-slot selection, even when the support is infinite. This is an order-based
selection of surviving slots, not an assumption that particular labels such
as `0` or `1` are present.

## Public declarations

When the slot order is locally finite and has a least element, the first
\(N\) surviving slots form an admissible selection. Its first two selected
slots satisfy
\[
i_1=\min R,\qquad
i_2=\min(R\setminus\{i_1\}),\qquad
i_1<i_2\ \text{ if } |R|\ge2,\qquad
|\operatorname{selectFirstNBySlotOrder}(N)|\le N.
\]

- `Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlot` returns
  the least selected child, with `⊥` on an empty selection;
  `.firstSelectedSlot_mem` gives membership for nonempty selections.
- `Combinatorics.Branching.Step.FiniteSelection.secondSelectedSlot` returns
  the least selected child after removing the first, with `⊥` when fewer than
  two children are selected; `.secondSelectedSlot_mem_of_card` proves the
  two selected slots are distinct members when the selection has cardinality
  at least two. `.firstSelectedSlot_lt_second_of_card` gives their strict
  order in the slot labels.
- `Combinatorics.Branching.Step.FiniteSelection.admitsFirstNBySlotOrder`
  proves lower finiteness for the slot key under a locally finite linear
  order with a least element.
- `Combinatorics.Branching.Step.FiniteSelection.firstNBySlotOrder N` selects
  the first `N` surviving slots, and `.firstNBySlotOrder_spec` gives its
  `IsFirstNBy` specification.
- `Combinatorics.Branching.Step.FiniteSelection.card_firstNBySlotOrder_eq_of_le_childCount`
  gives cardinality `N` when `N ≤ childCount ξ`; `.firstNBySlotOrder_isBoundedBy`
  gives the unconditional bound `card ≤ N`.
- `Combinatorics.Branching.Step.FiniteSelection.firstNBySlotOrder_nonempty_of_support_nonempty`
  gives a nonempty selection when `0 < N` and the support is nonempty.
-/

@[expose] public section

namespace Combinatorics.Branching

open Selection.NSelection

namespace Step.FiniteSelection

variable {α X : Type*}

/-- The least slot in a finite selected family, with a total value on the
empty-family case. -/
noncomputable def firstSelectedSlot [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  if h : (R ξ).Nonempty then (R ξ).min' h else ⊥

/-- The least selected slot after removing the first selected slot. The bottom
slot is used when fewer than two slots are selected. -/
noncomputable def secondSelectedSlot [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  let first := firstSelectedSlot R ξ
  if h : (R ξ).erase first |>.Nonempty then
    (R ξ).erase first |>.min' h
  else ⊥

theorem firstSelectedSlot_mem [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) : firstSelectedSlot R ξ ∈ R ξ := by
  rw [firstSelectedSlot, dite_eq_left hne]
  exact Finset.min'_mem _ _

theorem secondSelectedSlot_mem_of_card [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hcard : 2 ≤ (R ξ).card) :
    secondSelectedSlot R ξ ∈ R ξ ∧
      firstSelectedSlot R ξ ≠ secondSelectedSlot R ξ := by
  classical
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega))
  have herase : ((R ξ).erase (firstSelectedSlot R ξ)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hfirst]
    omega
  have hsecond : secondSelectedSlot R ξ ∈
      (R ξ).erase (firstSelectedSlot R ξ) := by
    have hvalue : secondSelectedSlot R ξ =
        ((R ξ).erase (firstSelectedSlot R ξ)).min' herase := by
      simp [secondSelectedSlot, herase]
    rw [hvalue]
    exact Finset.min'_mem _ _
  exact ⟨(Finset.mem_erase.mp hsecond).2,
    (Finset.mem_erase.mp hsecond).1.symm⟩

/-- The first and second selected slots are strictly ordered by their labels.
-/
theorem firstSelectedSlot_lt_second_of_card [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hcard : 2 ≤ (R ξ).card) :
    firstSelectedSlot R ξ < secondSelectedSlot R ξ := by
  have hslots := secondSelectedSlot_mem_of_card R ξ hcard
  have hnonempty : (R ξ).Nonempty := Finset.card_pos.mp (by omega)
  have hfirst : firstSelectedSlot R ξ = (R ξ).min' hnonempty := by
    simp [firstSelectedSlot, hnonempty]
  have hle : (R ξ).min' hnonempty ≤ secondSelectedSlot R ξ :=
    Finset.min'_le _ _ hslots.1
  have hle' : firstSelectedSlot R ξ ≤ secondSelectedSlot R ξ := by
    rw [hfirst]
    exact hle
  exact lt_of_le_of_ne hle' hslots.2

/-- The support of a step is lower-finite when ordered by its slot labels.
The least slot bounds every lower section inside a finite interval. -/
theorem admitsFirstNBySlotOrder [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] (N : ℕ) (ξ : Step α X) :
    AdmitsFirstNBy N (fun i : α => i) (support ξ) := by
  apply admitsFirstNBy_of_lowerFinite N
  intro p hp
  apply (Set.finite_Icc (⊥ : α) p).subset
  intro q hq
  have hqp : q ≤ p :=
    (Prod.Lex.le_iff.mp hq.2).elim le_of_lt (fun h => h.1.le)
  exact ⟨bot_le, hqp⟩

/-- Select the first `N` surviving slots in the abstract slot order. -/
noncomputable def firstNBySlotOrder [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] (N : ℕ) : Step.FiniteSelection α X :=
  firstNBy N (fun (_ : Step α X) (i : α) => i)
    (fun ξ => admitsFirstNBySlotOrder N ξ)

/-- The slot-order selection satisfies the intrinsic first-`N` specification. -/
theorem firstNBySlotOrder_spec [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] (N : ℕ) (ξ : Step α X) :
    IsFirstNBy N (fun i : α => i) (support ξ)
      (firstNBySlotOrder (α := α) (X := X) N ξ) := by
  exact firstNBy_spec N (fun (_ : Step α X) (i : α) => i)
    (fun ξ => admitsFirstNBySlotOrder N ξ) ξ

/-- If a step has at least `N` children, its first-`N` slot selection has
exactly `N` members. -/
theorem card_firstNBySlotOrder_eq_of_le_childCount
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    (N : ℕ) (ξ : Step α X) (hN : (N : ℕ∞) ≤ ξ.childCount) :
    (firstNBySlotOrder (α := α) (X := X) N ξ).card = N := by
  let selected := firstNBySlotOrder (α := α) (X := X) N ξ
  have hspec := firstNBySlotOrder_spec (α := α) (X := X) N ξ
  by_cases hfinite : (support ξ).Finite
  · have hcount : ξ.childCount = (hfinite.toFinset.card : ℕ∞) := by
      simp only [Step.childCount, hfinite.encard_eq_coe_toFinset_card]
    have hcard : N ≤ hfinite.toFinset.card := by
      exact_mod_cast (by simpa [hcount] using hN)
    change selected.card = N
    rw [hspec.card_finite hfinite, min_eq_left hcard]
  · have hinfinite : (support ξ).Infinite := hfinite
    rw [hspec.card_infinite hinfinite]

/-- The first-`N` slot selection always has capacity at most `N`. -/
theorem firstNBySlotOrder_isBoundedBy [LinearOrder α]
    [LocallyFiniteOrder α] [OrderBot α] (N : ℕ) :
    (firstNBySlotOrder (α := α) (X := X) N).IsBoundedBy N := by
  intro ξ
  exact (firstNBySlotOrder_spec (α := α) (X := X) N ξ).card_le

/-- A positive-capacity first-slot selection is nonempty whenever the step
has at least one child. -/
theorem firstNBySlotOrder_nonempty_of_support_nonempty
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    {N : ℕ} (hN : 0 < N) (ξ : Step α X)
    (hne : (support ξ).Nonempty) :
    (firstNBySlotOrder (α := α) (X := X) N ξ).Nonempty := by
  have hspec := firstNBySlotOrder_spec (α := α) (X := X) N ξ
  by_cases hfinite : (support ξ).Finite
  · have hsupport : hfinite.toFinset.Nonempty := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, hfinite.mem_toFinset.mpr hi⟩
    apply Finset.card_pos.mp
    rw [hspec.card_finite hfinite]
    exact lt_min_iff.mpr ⟨hN, Finset.card_pos.mpr hsupport⟩
  · have hinfinite : (support ξ).Infinite := hfinite
    apply Finset.card_pos.mp
    rw [hspec.card_infinite hinfinite]
    exact hN

end Step.FiniteSelection

end Combinatorics.Branching

end
