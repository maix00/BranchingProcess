/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.FirstEntrance

/-!
# Truncating a line at a generation

## Public declarations

In `Combinatorics.UlamHarris.RootIndexed.Line`:

* `truncate L n = firstEntrance (L ∪ {u : |u| = n})`.
* `isLine_truncate` proves this is a line, for any target set `L`.
* `truncate_precedes` and `truncate_precedes_generation` state `L_n ≼ L`
  and `L_n ≼ generation n`.
* `truncate_depth_le` bounds every retained address by `n`.
* `truncate_mono` states `n ≤ m → L_n ≼ L_m`.
* `mem_truncate_iff_of_lt` states `|u| < n → (u ∈ L_n ↔ u ∈ L)` for a line `L`.
* `truncate_meetsEveryRay` proves that `L_n` meets every infinite address path.

This is the line `L_n` of J. D. Biggins and A. E. Kyprianou, *Measure change
in multitype branching* (2004), §6, p. 557 and §14, p. 578,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
This deterministic module makes no optionality assertion. In particular,
Lemma 14.3's simple-line condition is separate from the construction.
-/

@[expose] public section

namespace Combinatorics.UlamHarris.RootIndexed.Line

variable {Root α : Type*} {L : Set (TreeNode Root α)}

/-- Stop at the original target or at generation `n`, whichever comes first. -/
def truncate (L : Set (TreeNode Root α)) (n : ℕ) : Set (TreeNode Root α) :=
  firstEntrance (L ∪ {u | u.2.length = n})

theorem isLine_truncate (L : Set (TreeNode Root α)) (n : ℕ) : IsLine (truncate L n) :=
  isLine_firstEntrance _

theorem truncate_precedes (L : Set (TreeNode Root α)) (n : ℕ) :
    Precedes (truncate L n) L := fun u hu => firstEntrance_precedes _ u (Or.inl hu)

theorem truncate_precedes_generation (L : Set (TreeNode Root α)) (n : ℕ) :
    Precedes (truncate L n) {u | u.2.length = n} :=
  fun u hu => firstEntrance_precedes _ u (Or.inr hu)

theorem truncate_depth_le {n : ℕ} {u : TreeNode Root α} (hu : u ∈ truncate L n) :
    u.2.length ≤ n := by
  by_contra h
  have hn : n < u.2.length := Nat.lt_of_not_ge h
  have hmem := (mem_firstEntrance_iff u).mp hu
  apply hmem.2 n hn
  exact Or.inr (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)])

theorem truncate_mono (L : Set (TreeNode Root α)) {n m : ℕ} (hnm : n ≤ m) :
    Precedes (truncate L n) (truncate L m) := by
  intro u hu
  rcases hu.1 with hL | hgen
  · exact truncate_precedes L n u hL
  · have hn : n ≤ u.2.length := hgen.symm ▸ hnm
    have hprefix : (u.1, u.2.take n) ∈ L ∪ {v | v.2.length = n} :=
      Or.inr (by simp [List.length_take, Nat.min_eq_left hn])
    obtain ⟨v, hv, hvp⟩ := firstEntrance_precedes _ _ hprefix
    exact ⟨v, hv, hvp.trans ⟨rfl, List.take_prefix _ _⟩⟩

theorem mem_truncate_iff_of_lt (hL : IsLine L) {n : ℕ} {u : TreeNode Root α}
    (hu : u.2.length < n) : u ∈ truncate L n ↔ u ∈ L := by
  constructor
  · intro h
    exact h.1.resolve_right (Nat.ne_of_lt hu)
  · intro h
    refine ⟨Or.inl h, fun v hv hvu => ?_⟩
    rcases hv with hv | hv
    · exact (hL.eq hv h hvu) ▸ IsAncestor.refl u
    · have hle := hvu.2.length_le
      change v.2.length = n at hv
      omega

/-- Every path meets a generation, so it meets the earlier truncated line. -/
theorem truncate_meetsEveryRay (L : Set (TreeNode Root α)) (n : ℕ)
    (C : Set (TreeNode Root α)) : MeetsEveryRay C (truncate L n) := by
  apply (truncate_precedes_generation L n).meetsEveryRay
  intro r f _
  exact ⟨n, length_lineagePrefix f n⟩

end Combinatorics.UlamHarris.RootIndexed.Line

end
