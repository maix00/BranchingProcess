/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Order
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Data.Nat.Find

/-!
# First entrance into a set of tree addresses

## Public declarations

In `Combinatorics.UlamHarris.RootIndexed.Line`:

* `firstEntrance A` consists of the ancestry-minimal elements of `A`, using
  Mathlib `Minimal` with the existing ancestry relation.
* `mem_firstEntrance_iff` states `u ∈ firstEntrance A ↔ u ∈ A ∧
  ∀ k < |u|, (u.1, u.2.take k) ∉ A`.
* `isLine_firstEntrance` proves that first entrance is a line.
* `firstEntrance_eq` states `firstEntrance L = L` for an existing line.
* `descendantClosure_firstEntrance` states `D_(firstEntrance A) = D_A`.
* `precedes_firstEntrance_iff` states `L ≼ firstEntrance A ↔ L ≼ A`.
* `firstEntrance_precedes` states `firstEntrance A ≼ A`.
* `firstEntrance_precedes_of_subset` states `A ⊆ B → firstEntrance B ≼ firstEntrance A`.
* `firstEntrance_inter_of_ancestorClosed` states
  `firstEntrance (C ∩ A) = C ∩ firstEntrance A` when `C` contains its ancestors.

This is the deterministic part of the threshold lines `I[t]` in J. D. Biggins
and A. E. Kyprianou, *Measure change in multitype branching* (2004), §6,
p. 557, before Proposition 6.1,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
Targets and root/child types are arbitrary; no law or coverage is assumed.
-/

@[expose] public section

namespace Combinatorics.UlamHarris.RootIndexed.Line

variable {Root α : Type*} {A B : Set (TreeNode Root α)}

/-- Ancestry-minimal target nodes, using native minimality. -/
def firstEntrance (A : Set (TreeNode Root α)) : Set (TreeNode Root α) :=
  {u | @Minimal (TreeNode Root α) ⟨IsAncestor⟩ (· ∈ A) u}

theorem mem_firstEntrance_iff (u : TreeNode Root α) :
    u ∈ firstEntrance A ↔ u ∈ A ∧
      ∀ k < u.2.length, (u.1, u.2.take k) ∉ A := by
  constructor
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, fun k hk hprefix => ?_⟩
    have hback := hmin hprefix ⟨rfl, List.take_prefix k u.2⟩
    have hlen := hback.2.length_le
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hlen
    omega
  · rintro ⟨hu, hprefix⟩
    refine ⟨hu, fun v hv hvu => ?_⟩
    have heq : v = u := by
      by_contra hne
      have hlt : v.2.length < u.2.length := by
        have hle := hvu.2.length_le
        have hlen : v.2.length ≠ u.2.length := by
          intro h
          exact hne (Prod.ext hvu.1 (hvu.2.eq_of_length h))
        omega
      have hp : (u.1, u.2.take v.2.length) = v :=
        Prod.ext hvu.1.symm (List.prefix_iff_eq_take.mp hvu.2).symm
      exact hprefix _ hlt (hp.symm ▸ hv)
    exact heq ▸ IsAncestor.refl u

theorem isLine_firstEntrance (A : Set (TreeNode Root α)) : IsLine (firstEntrance A) := by
  rw [isLine_iff]
  intro u hu v hv huv
  exact huv.antisymm (hv.2 hu.1 huv)

theorem firstEntrance_eq {L : Set (TreeNode Root α)} (hL : IsLine L) :
    firstEntrance L = L := by
  ext u
  constructor
  · exact fun h => h.1
  · intro hu
    exact ⟨hu, fun v hv hvu => (hL.eq hv hu hvu) ▸ IsAncestor.refl u⟩

/-- Every finite ancestral path meeting the target has a first target. -/
theorem descendantClosure_firstEntrance (A : Set (TreeNode Root α)) :
    descendantClosure (firstEntrance A) = descendantClosure A := by
  classical
  apply Set.Subset.antisymm
  · rintro v ⟨u, hu, huv⟩
    exact ⟨u, hu.1, huv⟩
  · intro v hv
    have hex : ∃ k, k ≤ v.2.length ∧ (v.1, v.2.take k) ∈ A := by
      obtain ⟨u, hu, huv⟩ := hv
      refine ⟨u.2.length, huv.2.length_le, ?_⟩
      have hp : (v.1, v.2.take u.2.length) = u :=
        Prod.ext huv.1.symm (List.prefix_iff_eq_take.mp huv.2).symm
      exact hp.symm ▸ hu
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    refine ⟨(v.1, v.2.take k), (mem_firstEntrance_iff _).mpr ⟨hk.2, ?_⟩,
      rfl, List.take_prefix k v.2⟩
    intro j hj hjA
    have hjk : j < k := lt_of_lt_of_le hj (List.length_take_le _ _)
    apply Nat.find_min hex hjk
    exact ⟨(Nat.le_of_lt hjk).trans hk.1,
      by simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjk)] using hjA⟩

theorem firstEntrance_precedes (A : Set (TreeNode Root α)) : Precedes (firstEntrance A) A := by
  rw [precedes_iff_subset_descendantClosure, descendantClosure_firstEntrance]
  exact subset_descendantClosure A

/-- Testing first entrance is equivalent to testing the entire target set. -/
theorem precedes_firstEntrance_iff {L : Set (TreeNode Root α)} :
    Precedes L (firstEntrance A) ↔ Precedes L A := by
  constructor
  · exact fun h => h.trans (firstEntrance_precedes A)
  · exact fun h u hu => h u hu.1

theorem firstEntrance_precedes_of_subset (hAB : A ⊆ B) :
    Precedes (firstEntrance B) (firstEntrance A) := by
  intro u hu
  exact firstEntrance_precedes B u (hAB hu.1)

/-- Restricting to a realized ancestor-closed tree commutes with first entrance. -/
theorem firstEntrance_inter_of_ancestorClosed (C : Set (TreeNode Root α))
    (hC : @IsLowerSet (TreeNode Root α) ⟨IsAncestor⟩ C) :
    firstEntrance (C ∩ A) = C ∩ firstEntrance A := by
  ext u
  constructor
  · intro hu
    exact ⟨hu.1.1, hu.1.2, fun v hv hvu => hu.2 ⟨hC hvu hu.1.1, hv⟩ hvu⟩
  · rintro ⟨huC, hu⟩
    exact ⟨⟨huC, hu.1⟩, fun _ hv hvu => hu.2 hv.2 hvu⟩

end Combinatorics.UlamHarris.RootIndexed.Line

end
