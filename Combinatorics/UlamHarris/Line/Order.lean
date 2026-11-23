/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Coverage

/-!
# Ancestral precedence of lines

## Public declarations

In `Combinatorics.UlamHarris.RootIndexed.Line`:

* `Precedes L M` means `∀ v ∈ M, ∃ u ∈ L, IsAncestor u v`.
  `Precedes.refl` and `Precedes.trans` prove reflexivity and transitivity on
  arbitrary node sets; `Precedes.antisymm` proves antisymmetry on lines.
* `precedes_iff_prefix` states `L ≼ M ↔ ∀ v ∈ M, ∃ n ≤ |v.2|,
  (v.1, v.2.take n) ∈ L`, using the finite ancestral path of each node.
* `descendantClosure L = {v | ∃ u ∈ L, IsAncestor u v}` includes `L` itself;
  `subset_descendantClosure` states this inclusion.
  `precedes_iff_subset_descendantClosure` identifies precedence with
  `M ⊆ descendantClosure L`.
* `mem_descendantClosure_generation_iff` states `v ∈ D_{generation n} ↔ n ≤ |v.2|`.
* `Precedes.meetsEveryRay` states that if `M` meets every realized infinite
  path and `L` precedes `M`, then `L` also meets every such path.

Root and child-index types are arbitrary. Precedence is not set inclusion:
its direction is from the earlier line to the later line. This is the
ancestral ordering used in A. E. Kyprianou, *Martingale convergence and the
stopped branching random walk* (2000), §2, pp. 408–409,
[DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
-/

@[expose] public section

namespace Combinatorics.UlamHarris.RootIndexed.Line

variable {Root α : Type*} {L M N : Set (TreeNode Root α)}

/-- Every member of `M` has an ancestor in `L`. -/
def Precedes (L M : Set (TreeNode Root α)) : Prop :=
  ∀ v ∈ M, ∃ u ∈ L, IsAncestor u v

theorem Precedes.refl (L : Set (TreeNode Root α)) : Precedes L L :=
  fun v hv => ⟨v, hv, IsAncestor.refl v⟩

theorem Precedes.trans (hLM : Precedes L M) (hMN : Precedes M N) : Precedes L N := by
  intro v hv
  obtain ⟨m, hm, hmv⟩ := hMN v hv
  obtain ⟨u, hu, hum⟩ := hLM m hm
  exact ⟨u, hu, hum.trans hmv⟩

theorem Precedes.antisymm (hLM : Precedes L M) (hML : Precedes M L)
    (hL : IsLine L) (hM : IsLine M) : L = M := by
  have incl : ∀ {A B : Set (TreeNode Root α)},
      Precedes A B → Precedes B A → IsLine A → A ⊆ B := by
    intro A B hAB hBA hA a ha
    obtain ⟨b, hb, hba⟩ := hBA a ha
    obtain ⟨c, hc, hcb⟩ := hAB b hb
    have hca : c = a := hA.eq hc ha (hcb.trans hba)
    subst c
    exact (hcb.antisymm hba) ▸ hb
  exact Set.Subset.antisymm (incl hLM hML hL) (incl hML hLM hM)

/-- Precedence can be checked using the finite list of prefixes of each tested node. -/
theorem precedes_iff_prefix : Precedes L M ↔
    ∀ v ∈ M, ∃ n ≤ v.2.length, (v.1, v.2.take n) ∈ L := by
  constructor
  · intro h v hv
    obtain ⟨u, hu, huv⟩ := h v hv
    refine ⟨u.2.length, huv.2.length_le, ?_⟩
    have heq : (v.1, v.2.take u.2.length) = u :=
      Prod.ext huv.1.symm (List.prefix_iff_eq_take.mp huv.2).symm
    exact heq.symm ▸ hu
  · intro h v hv
    obtain ⟨n, hn, hu⟩ := h v hv
    exact ⟨(v.1, v.2.take n), hu, rfl, List.take_prefix n v.2⟩

/-- The union of descendant subtrees, including their roots on the line. -/
def descendantClosure (L : Set (TreeNode Root α)) : Set (TreeNode Root α) :=
  {v | ∃ u ∈ L, IsAncestor u v}

theorem subset_descendantClosure (L : Set (TreeNode Root α)) :
    L ⊆ descendantClosure L := fun u hu => ⟨u, hu, IsAncestor.refl u⟩

theorem precedes_iff_subset_descendantClosure :
    Precedes L M ↔ M ⊆ descendantClosure L := Iff.rfl

/-- A generation cuts precisely the addresses of at least that depth. -/
theorem mem_descendantClosure_generation_iff (n : ℕ) (v : TreeNode Root α) :
    v ∈ descendantClosure {u | u.2.length = n} ↔ n ≤ v.2.length := by
  constructor
  · rintro ⟨u, hu, huv⟩
    exact hu ▸ huv.2.length_le
  · intro hn
    refine ⟨(v.1, v.2.take n), ?_, rfl, List.take_prefix _ _⟩
    simp [List.length_take, Nat.min_eq_left hn]

/-- An earlier line covers every infinite path covered by a later line. -/
theorem Precedes.meetsEveryRay (hLM : Precedes L M) {C : Set (TreeNode Root α)}
    (hM : MeetsEveryRay C M) : MeetsEveryRay C L := by
  intro r f hf
  obtain ⟨n, hn⟩ := hM r f hf
  obtain ⟨⟨s, u⟩, hu, hanc⟩ := hLM (r, lineagePrefix f n) hn
  have hsr : s = r := hanc.1
  subst s
  have hlen : u.length ≤ n := by simpa using hanc.2.length_le
  have heq : u = lineagePrefix f u.length :=
    (List.prefix_of_prefix_length_le hanc.2
      (lineagePrefix_prefix f hlen) (by simp)).eq_of_length (by simp)
  exact ⟨u.length, heq ▸ hu⟩

end Combinatorics.UlamHarris.RootIndexed.Line

end
