/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Relation
public import Mathlib.Order.Antichain

/-!
# Lines of tree addresses

## Public declarations

In `Combinatorics.UlamHarris`, `IsLine L` is Mathlib's
`IsAntichain List.IsPrefix L`: distinct members of `L` are incomparable for
ancestry. `isLine_iff` states `IsLine L ↔ ∀ u ∈ L, ∀ v ∈ L, u <+: v → u = v`.
`isLine_generation` proves that `{u | u.length = n}` is a line.
`IsLine.append` preserves a line under `u ↦ w ++ u`.

In `Combinatorics.UlamHarris.RootIndexed`:

* `IsLine L` is `IsAntichain IsAncestor L`; `isLine_iff` gives the same
  comparable-members-equal criterion, and `isLine_iff_fibers` identifies it
  with `∀ r, UlamHarris.IsLine {u | (r,u) ∈ L}`.
* `isLine_generation` proves `{p | p.2.length = n}` is a line;
  `isLine_of_depth` gives the conclusion for any subset of that generation.
* `IsLine.eq_of_common_descendant` states that two members of a line having
  a common descendant are equal. `IsLine.appendAddresses_injective` states
  that concatenation `(p,v) ↦ (p.1.1,p.1.2 ++ v)` is injective on `L × List α`.

All types of roots and child indices are arbitrary. Empty sets, singletons,
and subsets use Mathlib's `IsAntichain.empty`, `IsAntichain.singleton`, and
`IsAntichain.subset` directly. Lines carry neither a finiteness requirement
nor a requirement to meet all infinite paths.

The terminology follows A. E. Kyprianou, *Martingale convergence and the
stopped branching random walk* (2000), §2, p. 408,
[DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
Only the deterministic ancestry definition is used here; optionality is a
separate probabilistic condition.
-/

@[expose] public section

namespace Combinatorics.UlamHarris

variable {α : Type*}

/-- A line is an ancestry antichain, with no coverage or finiteness condition. -/
abbrev IsLine (L : Set (TreeNode α)) : Prop := IsAntichain List.IsPrefix L

theorem isLine_iff {L : Set (TreeNode α)} :
    IsLine L ↔ ∀ u ∈ L, ∀ v ∈ L, u <+: v → u = v := by
  constructor
  · intro h u hu v hv huv
    exact h.eq hu hv huv
  · intro h u hu v hv hne huv
    exact hne (h u hu v hv huv)

/-- Every fixed generation is a line. -/
theorem isLine_generation (n : ℕ) : IsLine {u : TreeNode α | u.length = n} := by
  rw [isLine_iff]
  intro u hu v hv huv
  exact huv.eq_of_length (hu.trans hv.symm)

/-- A line in a subtree remains a line after restoring its common prefix. -/
theorem IsLine.append {L : Set (TreeNode α)} (h : IsLine L) (w : TreeNode α) :
    IsLine ((fun u => w ++ u) '' L) :=
  h.image _ (fun _ _ huv => (List.prefix_append_right_inj w).mp huv)

namespace RootIndexed

variable {Root : Type*}

/-- A line in a forest is an antichain for root-preserving ancestry. -/
abbrev IsLine (L : Set (TreeNode Root α)) : Prop := IsAntichain IsAncestor L

theorem isLine_iff {L : Set (TreeNode Root α)} :
    IsLine L ↔ ∀ p ∈ L, ∀ q ∈ L, IsAncestor p q → p = q := by
  constructor
  · intro h p hp q hq hpq
    exact h.eq hp hq hpq
  · intro h p hp q hq hne hpq
    exact hne (h p hp q hq hpq)

/-- Distinct roots never impose an ancestry constraint on each other. -/
theorem isLine_iff_fibers {L : Set (TreeNode Root α)} :
    IsLine L ↔ ∀ r, UlamHarris.IsLine {u | (r, u) ∈ L} := by
  simp only [isLine_iff, UlamHarris.isLine_iff]
  constructor
  · intro h r u hu v hv huv
    exact congrArg Prod.snd (h (r, u) hu (r, v) hv ⟨rfl, huv⟩)
  · rintro h ⟨r, u⟩ hu ⟨s, v⟩ hv ⟨hrs, huv⟩
    change r = s at hrs
    subst s
    exact Prod.ext rfl (h r u hu v hv huv)

theorem isLine_of_depth {L : Set (TreeNode Root α)} {n : ℕ}
    (hdepth : ∀ p ∈ L, p.2.length = n) : IsLine L := by
  rw [isLine_iff]
  intro p hp q hq hpq
  exact Prod.ext hpq.1 (hpq.2.eq_of_length ((hdepth p hp).trans (hdepth q hq).symm))

theorem isLine_generation (n : ℕ) :
    IsLine {p : TreeNode Root α | p.2.length = n} :=
  isLine_of_depth (fun _ hp => hp)

/-- Descendant subtrees rooted on a line have disjoint carriers. -/
theorem IsLine.eq_of_common_descendant {L : Set (TreeNode Root α)} (hL : IsLine L)
    {p q v : TreeNode Root α} (hp : p ∈ L) (hq : q ∈ L)
    (hpv : IsAncestor p v) (hqv : IsAncestor q v) : p = q := by
  have hr : p.1 = q.1 := hpv.1.trans hqv.1.symm
  rcases List.prefix_or_prefix_of_prefix hpv.2 hqv.2 with h | h
  · exact hL.eq hp hq ⟨hr, h⟩
  · exact (hL.eq hq hp ⟨hr.symm, h⟩).symm

/-- Appending arbitrary suffixes to distinct line members preserves distinctness. -/
theorem IsLine.appendAddresses_injective {L : Set (TreeNode Root α)} (hL : IsLine L) :
    Function.Injective (fun p : L × UlamHarris.TreeNode α =>
      (p.1.1.1, p.1.1.2 ++ p.2)) := by
  rintro ⟨⟨p, hp⟩, u⟩ ⟨⟨q, hq⟩, v⟩ heq
  change (p.1, p.2 ++ u) = (q.1, q.2 ++ v) at heq
  have hpq : p = q := hL.eq_of_common_descendant (v := (p.1, p.2 ++ u)) hp hq
    ⟨rfl, List.prefix_append _ _⟩
    (by rw [heq]; exact ⟨rfl, List.prefix_append _ _⟩)
  subst q
  have huv : u = v := List.append_cancel_left (congrArg Prod.snd heq)
  subst v
  rfl

end RootIndexed
end Combinatorics.UlamHarris

end
