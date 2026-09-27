import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Abstract countable ordered child slots

The ordered child slots used by finite-`N` selection need not literally be
`ℕ`. A linear locally finite order with a least element and no greatest
element has order type `ℕ`; mathlib supplies the order isomorphism. The first
`N` slots and their exhaustion are defined through that isomorphism.
-/

namespace Combinatorics.Branching

open scoped BigOperators

/-- The mathlib-derived order isomorphism from an abstract slot order to
`ℕ`. No additional slot-ranking structure is introduced. -/
noncomputable def slotOrderIsoNat (α : Type*) [LinearOrder α]
    [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α] : α ≃o ℕ := by
  letI := LinearLocallyFiniteOrder.succOrder α
  letI := LinearLocallyFiniteOrder.predOrder α
  exact orderIsoNatOfLinearSuccPredArch

/-- The finite set of the first `N` slots in an abstract order of type
`ℕ`. -/
noncomputable def firstSlots (α : Type*) [LinearOrder α]
    [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (N : ℕ) : Finset α :=
  (Finset.range N).map (slotOrderIsoNat α).symm.toEmbedding

theorem mem_firstSlots_iff
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] {i : α} {N : ℕ} :
    i ∈ firstSlots α N ↔ slotOrderIsoNat α i < N := by
  simp [firstSlots]

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
  simp [firstSlots]

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
theorem mem_firstSlots_succ_rank
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (i : α) :
    i ∈ firstSlots α (slotOrderIsoNat α i + 1) := by
  rw [mem_firstSlots_iff]
  exact Nat.lt_succ_self _

/-- The increasing finite prefixes exhaust all ordered slots. -/
theorem iUnion_firstSlots
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] :
    (⋃ N : ℕ, (firstSlots α N : Set α)) = Set.univ := by
  ext i
  simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_univ, iff_true]
  exact ⟨slotOrderIsoNat α i + 1, mem_firstSlots_succ_rank i⟩

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
