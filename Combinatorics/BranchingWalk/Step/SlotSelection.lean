/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.FiniteSelection
public import Combinatorics.BranchingWalk.Step.Count
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Selecting the first slots of a branching step

In a locally finite linear order with a least slot, every step admits a first
`N`-slot selection, even when the support is infinite. This is an order-based
selection of surviving slots, not an assumption that particular labels such
as `0` or `1` are present.
-/

@[expose] public section

namespace Combinatorics.Branching

open Selection.NSelection

namespace Step.FiniteSelection

variable {α X : Type*}

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
