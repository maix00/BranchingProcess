/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic

/-!
# Deterministic Ulam--Harris trees

`Tree α` is a deterministic rooted tree of addresses `TreeNode α`. Its carrier
contains the root, is parent closed, and is closed under smaller sibling
labels. The structure is not assumed to be finite, countable, or locally
finite. This file contains only the deterministic tree and root-indexed tree
definitions; their measurable spaces live in `Tree/MeasurableSpace.lean`.
-/

@[expose] public section

/-! ### Families indexed by several initial ancestors

The root-indexed tree is an indexed family of ordinary trees. Its definition
and elementary carrier predicates live beside the single-root definition.
-/

namespace Combinatorics

namespace UlamHarris

/-- A rooted tree of addresses. The carrier contains the root, is parent
closed, and for ordered child labels contains every smaller sibling below a
survive child. `Set (List α)` is only the underlying carrier of this
structure. -/
structure Tree (α : Type*) [LT α] where
  carrier : Set (List α)
  root_mem : [] ∈ carrier
  parent_closed : ∀ {u v : List α}, u ++ v ∈ carrier → u ∈ carrier
  sibling_closed : ∀ {u : List α} {i j : α},
    u ++ [j] ∈ carrier → i < j → u ++ [i] ∈ carrier

/-- Two trees are equal as soon as their carriers are equal: the remaining
fields of `Tree` are propositions and hence proof irrelevant. -/
@[ext]
theorem Tree.ext {α : Type*} [LT α] {T T' : Tree α}
    (h : T.carrier = T'.carrier) : T = T' := by
  cases T
  cases T'
  simp only at h
  cases h
  rfl

@[simp] theorem Tree.root_mem' {α : Type*} [LT α]
    (T : Tree α) :
    [] ∈ T.carrier := T.root_mem

theorem Tree.mem_parent {α : Type*} [LT α] (T : Tree α)
    {u v : List α} (h : u ++ v ∈ T.carrier) : u ∈ T.carrier :=
  T.parent_closed h

namespace RootIndexed

/-- A deterministic tree for every initial ancestor. -/
abbrev Tree (Root α : Type*) [LT α] := Root → UlamHarris.Tree α

namespace Tree

variable {Root NewRoot α : Type*} [LT α]

/-- Every initial ancestor carries a realized root. -/
theorem root_mem (T : RootIndexed.Tree Root α) (r : Root) :
    [] ∈ (T r).carrier :=
  (T r).root_mem

/-- Parent closure holds separately in every root-indexed tree. -/
theorem mem_parent (T : RootIndexed.Tree Root α) (r : Root)
    {u v : List α} (h : u ++ v ∈ (T r).carrier) : u ∈ (T r).carrier :=
  UlamHarris.Tree.mem_parent (T r) h

/-- Sibling closure holds separately in every root-indexed tree. -/
theorem sibling_closed (T : RootIndexed.Tree Root α) (r : Root)
    {u : List α} {i j : α} (h : u ++ [j] ∈ (T r).carrier) (hij : i < j) :
    u ++ [i] ∈ (T r).carrier :=
  (T r).sibling_closed h hij

@[ext (iff := false)]
theorem ext {S T : RootIndexed.Tree Root α} (h : ∀ r, S r = T r) : S = T := by
  funext r
  exact h r

/-- Reindex a family of trees along a map of initial ancestors. -/
def reindex (f : NewRoot → Root) (T : RootIndexed.Tree Root α) :
    RootIndexed.Tree NewRoot α :=
  fun r => T (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root) (T : RootIndexed.Tree Root α)
    (r : NewRoot) : T.reindex f r = T (f r) := rfl

@[simp]
theorem reindex_id (T : RootIndexed.Tree Root α) : T.reindex id = T := rfl

@[simp]
theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (T : RootIndexed.Tree Root α) :
    (T.reindex f).reindex g = T.reindex (f ∘ g) := rfl

abbrev FiniteRootTree (m : ℕ) (α : Type*) [LT α] := RootIndexed.Tree (Fin m) α

abbrev CountableRootTree (α : Type*) [LT α] := RootIndexed.Tree ℕ α

theorem finiteRootTree_ext {m : ℕ} {S T : FiniteRootTree m α}
    (h : ∀ r, S r = T r) : S = T := ext h

end Tree

end RootIndexed

end UlamHarris

end Combinatorics

end
