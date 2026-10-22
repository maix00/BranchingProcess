/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Decomposing a positive composition at its first part

The public definitions and theorems in this file are:

- `Composition.firstPartIndex`: for a composition of $n>0$, its first
  positive part, encoded as one less than a member of `Fin n`.
- `Composition.tailAfterFirst`: the composition obtained by removing its
  first part.
- `Composition.prependPositive`: prepend a positive first part to a
  composition of the remaining integer.
- `Composition.firstPartIndex_prependPositive`: prepending and then reading
  the first part recovers its index.
- `Composition.tailAfterFirst_prependPositive`: prepending and then removing
  the first part recovers the tail composition.
- `Composition.prependPositive_firstPartIndex_tail`: any positive composition
  is reconstructed from its first part and tail.
- `Composition.firstPartEquiv`: compositions of $n>0$ correspond to a
  positive first part $r+1$ and a composition of $n-r-1$.
- `Composition.sum_firstPart`: any finite sum over positive compositions
  can be regrouped by its first part and remaining composition.
- `Composition.blocks_prependPositive`: the block list of the prepended
  composition is the positive first part followed by the tail blocks.
- `Composition.length_prependPositive`: prepending increases the number of
  parts by one.
- `Composition.prod_blocks_prependPositive`: the product of block weights
  factors into the first-part weight and the product over tail blocks.

This finite decomposition is useful when regrouping composition sums by
their first part, including the coefficient recurrence of the
Sparre--Andersen identity.
-/

@[expose] public section

namespace Composition

/-- The first part of a positive composition, represented as a member of
`Fin n` whose value is one less than that part. -/
def firstPartIndex {n : ℕ} (c : Composition n) (hn : 0 < n) : Fin n := by
  have hne : c.blocks ≠ [] := by
    intro h
    have := (c.blocks_eq_nil).mp h
    omega
  have hpos : 0 < c.blocks.head hne :=
    c.blocks_pos (List.head_mem hne)
  have hle : c.blocks.head hne ≤ n := by
    have h := List.le_sum_of_mem (List.head_mem hne)
    rwa [c.blocks_sum] at h
  exact ⟨c.blocks.head hne - 1, by omega⟩

/-- Removing the first part leaves a composition of the remaining integer. -/
def tailAfterFirst {n : ℕ} (c : Composition n) (hn : 0 < n) :
    Composition (n - ((c.firstPartIndex hn).val + 1)) := by
  have hne : c.blocks ≠ [] := by
    intro h
    have := (c.blocks_eq_nil).mp h
    omega
  have hsum : c.blocks.head hne + c.blocks.tail.sum = n := by
    calc
      c.blocks.head hne + c.blocks.tail.sum =
          (c.blocks.head hne :: c.blocks.tail).sum := by rw [List.sum_cons]
      _ = c.blocks.sum := by rw [List.cons_head_tail hne]
      _ = n := c.blocks_sum
  have hhead : (c.firstPartIndex hn).val + 1 = c.blocks.head hne := by
    have hpos : 0 < c.blocks.head hne :=
      c.blocks_pos (List.head_mem hne)
    simp only [firstPartIndex]
    omega
  refine ⟨c.blocks.tail, ?_, ?_⟩
  · intro i hi
    exact c.blocks_pos (List.mem_of_mem_tail hi)
  · rw [hhead]
    omega

/-- Prepend a positive first part to a composition of the remaining
integer. -/
def prependPositive {n : ℕ} (_hn : 0 < n) (r : Fin n)
    (d : Composition (n - (r.val + 1))) : Composition n where
  blocks := (r.val + 1) :: d.blocks
  blocks_pos := by
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · omega
    · exact d.blocks_pos hi
  blocks_sum := by
    simp only [List.sum_cons, d.blocks_sum]
    have hr : r.val + 1 ≤ n := by omega
    omega

@[simp] theorem blocks_prependPositive {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1))) :
    (prependPositive hn r d).blocks = (r.val + 1) :: d.blocks := rfl

@[simp] theorem length_prependPositive {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1))) :
    (prependPositive hn r d).length = d.length + 1 := by
  simp [Composition.length]

@[simp] theorem prod_blocks_prependPositive {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1)))
    {R : Type*} [CommMonoid R] (w : ℕ → R) :
    ((prependPositive hn r d).blocks.map w).prod =
      w (r.val + 1) * (d.blocks.map w).prod := by
  simp

/-- The first part of a prepended composition is the prepended part. -/
theorem firstPartIndex_prependPositive {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1))) :
    (prependPositive hn r d).firstPartIndex hn = r := by
  apply Fin.ext
  simp [firstPartIndex, prependPositive]

/-- Removing the first part of a prepended composition returns the tail. -/
theorem tailAfterFirst_prependPositive {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1))) :
    (prependPositive hn r d).tailAfterFirst hn =
      d.cast (by rw [firstPartIndex_prependPositive]) := by
  apply Composition.ext
  simp [tailAfterFirst, prependPositive, Composition.cast]

/-- Every positive composition is its first part prepended to its tail. -/
theorem prependPositive_firstPartIndex_tail {n : ℕ}
    (c : Composition n) (hn : 0 < n) :
    prependPositive hn (c.firstPartIndex hn) (c.tailAfterFirst hn) = c := by
  apply Composition.ext
  have hne : c.blocks ≠ [] := by
    intro h
    have := (c.blocks_eq_nil).mp h
    omega
  have hhead : (c.firstPartIndex hn).val + 1 = c.blocks.head hne := by
    have hpos : 0 < c.blocks.head hne :=
      c.blocks_pos (List.head_mem hne)
    simp only [firstPartIndex]
    omega
  simp only [prependPositive, tailAfterFirst, hhead]
  exact List.cons_head_tail hne

/-- A positive composition is equivalent to its first part and the
composition of the remaining integer. -/
def firstPartEquiv {n : ℕ} (hn : 0 < n) :
    Composition n ≃ Σ r : Fin n, Composition (n - (r.val + 1)) where
  toFun c := ⟨c.firstPartIndex hn, c.tailAfterFirst hn⟩
  invFun p := prependPositive hn p.1 p.2
  left_inv c := prependPositive_firstPartIndex_tail c hn
  right_inv p := by
    rcases p with ⟨r, d⟩
    apply Sigma.ext (firstPartIndex_prependPositive hn r d)
    change (prependPositive hn r d).tailAfterFirst hn ≍ d
    rw [tailAfterFirst_prependPositive]
    exact heq_of_eq (by apply Composition.ext; rfl)

/-- Regroup a sum over compositions by the positive first part. -/
theorem sum_firstPart {n : ℕ} (hn : 0 < n)
    {R : Type*} [AddCommMonoid R] (f : Composition n → R) :
    ∑ c : Composition n, f c =
      ∑ r : Fin n, ∑ d : Composition (n - (r.val + 1)),
        f (prependPositive hn r d) := by
  rw [Fintype.sum_equiv (firstPartEquiv hn) f
    (fun p => f ((firstPartEquiv hn).symm p)) (by intro c; simp)]
  rw [Fintype.sum_sigma]
  rfl

end Composition

end
